from __future__ import annotations

import asyncio
import glob
import logging
import os
import re
import shutil
from datetime import datetime
from typing import TYPE_CHECKING, Any, Dict, List, Optional, Tuple
from zipfile import ZipFile

import requests
from tornado.ioloop import IOLoop

try:
    from PIL import Image as PilImage
    _PIL_AVAILABLE = True
except ImportError:
    _PIL_AVAILABLE = False

if TYPE_CHECKING:
    from confighelper import ConfigHelper
    from .webcam import WebcamManager
    from websockets import WebRequest
    from . import shell_command
    from . import klippy_apis
    from . import database

    APIComp = klippy_apis.KlippyAPI
    SCMDComp = shell_command.ShellCommandFactory
    DBComp = database.MoonrakerDatabase


class Timelapse:

    DEFAULT_CONFIG: Dict[str, Any] = {
        'enabled': True,
        'mode': "layermacro",
        'camera': "",
        'snapshoturl': "http://localhost:8080/?action=snapshot",
        'stream_delay_compensation': 0.05,
        'gcode_verbose': False,
        'parkhead': False,
        'parkpos': "back_left",
        'park_custom_pos_x': 10.0,
        'park_custom_pos_y': 10.0,
        'park_custom_pos_dz': 0.0,
        'park_travel_speed': 100,
        'park_retract_speed': 15,
        'park_extrude_speed': 15,
        'park_retract_distance': 1.0,
        'park_extrude_distance': 1.0,
        'park_time': 0.1,
        'fw_retract': False,
        'hyperlapse_cycle': 30,
        'autorender': True,
        'constant_rate_factor': 23,
        'output_framerate': 30,
        'pixelformat': "yuv420p",
        'time_format_code': "%Y%m%d_%H%M",
        'extraoutputparams': "",
        'variable_fps': False,
        'targetlength': 10,
        'variable_fps_min': 5,
        'variable_fps_max': 60,
        'rotation': 0,
        'flip_x': False,
        'flip_y': False,
        'duplicatelastframe': 5,
        'previewimage': True,
        'saveframes': False,
    }

    SETTINGS_WITH_GCODE_CHANGE: frozenset = frozenset({
        'enabled', 'parkhead', 'parkpos',
        'park_custom_pos_x', 'park_custom_pos_y', 'park_custom_pos_dz',
        'park_travel_speed', 'park_retract_speed', 'park_extrude_speed',
        'park_retract_distance', 'park_extrude_distance', 'park_time',
        'fw_retract',
    })

    def __init__(self, confighelper: ConfigHelper) -> None:
        self.renderisrunning = False
        self.saveisrunning = False
        self.takingframe = False
        self.framecount = 0
        self.lastframefile = ""
        self.lastrenderprogress = 0
        self.lastcmdreponse = ""
        self.byrendermacro = False
        self.hyperlapserunning = False
        self.printing = False
        self.no_webcam_db = False

        self.confighelper = confighelper
        self.server = confighelper.get_server()
        self.klippy_apis: APIComp = self.server.lookup_component('klippy_apis')
        self.database: DBComp = self.server.lookup_component("database")

        out_dir_cfg = confighelper.get("output_path", "~/timelapse/")
        temp_dir_cfg = confighelper.get(
            "frame_path", "/var/lib/moonraker/timelapse/frames/")
        self.ffmpeg_binary_path = confighelper.get(
            "ffmpeg_binary_path", "/usr/bin/ffmpeg")
        self.wget_skip_cert = confighelper.getboolean(
            "wget_skip_cert_check", False)

        self.config: Dict[str, Any] = dict(self.DEFAULT_CONFIG)

        dbconfig: Dict[str, Any] = self.database.get_item(
            "timelapse", "config", self.config)
        if isinstance(dbconfig, asyncio.Future):
            self.config.update(dbconfig.result())
        else:
            self.config.update(dbconfig)

        self._overwrite_db_config_with_confighelper()

        self.ffmpeg_installed = os.path.isfile(self.ffmpeg_binary_path)
        if not self.ffmpeg_installed:
            self.config['autorender'] = False
            logging.info(
                "timelapse: %s not found, "
                "please install ffmpeg to use render functionality",
                self.ffmpeg_binary_path,
            )

        self.out_dir = os.path.expanduser(os.path.join(out_dir_cfg, ''))
        self.temp_dir = os.path.expanduser(os.path.join(temp_dir_cfg, ''))
        os.makedirs(self.temp_dir, exist_ok=True)
        os.makedirs(self.out_dir, exist_ok=True)

        file_manager = self.server.lookup_component("file_manager")
        file_manager.register_directory(
            "timelapse", self.out_dir, full_access=True)
        file_manager.register_directory("timelapse_frames", self.temp_dir)

        self.server.register_notification("timelapse:timelapse_event")
        self.server.register_event_handler(
            "server:gcode_response", self.handle_gcode_response)
        self.server.register_event_handler(
            "server:status_update", self.handle_status_update)
        self.server.register_event_handler(
            "server:klippy_ready", self.handle_klippy_ready)
        self.server.register_remote_method(
            "timelapse_newframe", self.call_newframe)
        self.server.register_remote_method(
            "timelapse_saveFrames", self.call_save_frames_zip)
        self.server.register_remote_method(
            "timelapse_render", self.call_render)
        self.server.register_endpoint(
            "/machine/timelapse/render", ['POST'], self.render)
        self.server.register_endpoint(
            "/machine/timelapse/saveframes", ['POST'], self.save_frames_zip)
        self.server.register_endpoint(
            "/machine/timelapse/settings", ['GET', 'POST'],
            self.webrequest_settings)
        self.server.register_endpoint(
            "/machine/timelapse/lastframeinfo", ['GET'],
            self.webrequest_lastframeinfo)

    async def component_init(self) -> None:
        await self._get_webcam_config()

    def _overwrite_db_config_with_confighelper(self) -> None:
        type_getters = {
            str: self.confighelper.get,
            bool: self.confighelper.getboolean,
            int: self.confighelper.getint,
            float: self.confighelper.getfloat,
        }
        blocked: List[str] = []
        for key in self.confighelper.get_options():
            if key in self.config:
                getter = type_getters.get(type(self.config[key]))
                if getter is not None:
                    self.config[key] = getter(key)
                    blocked.append(key)
        self.config['blockedsettings'] = blocked
        logging.debug("timelapse blockedsettings: %s", blocked)

    async def _get_webcam_config(self) -> None:
        webcam_name = self.config['camera']
        try:
            wcmgr: WebcamManager = self.server.lookup_component("webcam")
            cams = wcmgr.get_webcams()

            if not cams:
                logging.info(
                    "timelapse: no camera configured, using fallback config")
                self._parse_webcam_config({
                    'snapshot_url': self.config['snapshoturl'],
                    'rotation': self.config['rotation'],
                    'flip_horizontal': self.config['flip_x'],
                    'flip_vertical': self.config['flip_y'],
                })
                return

            camera = (
                cams[webcam_name]
                if webcam_name and webcam_name in cams
                else next(iter(cams.values()))
            )
            self._parse_webcam_config(camera.as_dict())

        except Exception:
            logging.exception(
                "timelapse: error getting webcam config for '%s'", webcam_name)

    def _parse_webcam_config(self, webcamconfig: Dict[str, Any]) -> None:
        old = {
            'url': self.config['snapshoturl'],
            'flip_x': self.config['flip_x'],
            'flip_y': self.config['flip_y'],
            'rotation': self.config['rotation'],
        }

        url: str = webcamconfig['snapshot_url']
        if not url.startswith('http'):
            url = "http://localhost" + ("" if url.startswith('/') else "/") + url

        self.config['snapshoturl'] = self.confighelper.get('snapshoturl', url)
        self.config['flip_x'] = self.confighelper.getboolean(
            'flip_x', webcamconfig['flip_horizontal'])
        self.config['flip_y'] = self.confighelper.getboolean(
            'flip_y', webcamconfig['flip_vertical'])
        self.config['rotation'] = self.confighelper.getint(
            'rotation', webcamconfig['rotation'])

        new = {
            'url': self.config['snapshoturl'],
            'flip_x': self.config['flip_x'],
            'flip_y': self.config['flip_y'],
            'rotation': self.config['rotation'],
        }

        if old != new:
            logging.info(
                "timelapse: webcam config updated — url=%s flip_x=%s "
                "flip_y=%s rotation=%s",
                new['url'], new['flip_x'], new['flip_y'], new['rotation'],
            )

    async def webrequest_lastframeinfo(
            self, webrequest: WebRequest) -> Dict[str, Any]:
        return {
            'framecount': self.framecount,
            'lastframefile': self.lastframefile,
        }

    async def webrequest_settings(
            self, webrequest: WebRequest) -> Dict[str, Any]:
        if webrequest.get_action() != 'POST':
            return self.config

        args = webrequest.get_args()
        logging.debug("timelapse webrequest settings args: %s", args)

        type_getters = {
            str: webrequest.get,
            bool: webrequest.get_boolean,
            int: webrequest.get_int,
            float: webrequest.get_float,
        }

        gcodechange = False
        modechanged = False

        for setting in args:
            if setting not in self.config:
                continue
            if setting == "snapshoturl":
                logging.debug(
                    "timelapse: snapshoturl cannot be changed via webrequest")
                continue

            getter = type_getters.get(type(self.config[setting]))
            if getter is None:
                continue

            value = getter(setting)
            self.config[setting] = value
            self.database.insert_item("timelapse", "config.%s" % setting, value)

            if setting == "camera":
                if not self.no_webcam_db:
                    await self._get_webcam_config()
                else:
                    logging.info(
                        "timelapse: webcam namespace not initialized, "
                        "please restart moonraker")

            if setting in self.SETTINGS_WITH_GCODE_CHANGE:
                gcodechange = True
            if setting == "mode":
                modechanged = True

            logging.debug(
                "timelapse: setting changed — %s=%s (%s)",
                setting, value, type(self.config[setting]).__name__,
            )

        ioloop = IOLoop.current()
        if modechanged:
            if self.config['mode'] == "hyperlapse":
                if not self.hyperlapserunning and self.printing:
                    ioloop.spawn_callback(self.start_hyperlapse)
            elif self.hyperlapserunning:
                ioloop.spawn_callback(self.stop_hyperlapse)

        if gcodechange:
            ioloop.spawn_callback(self._set_gcode_variables)

        return self.config

    async def handle_klippy_ready(self) -> None:
        ioloop = IOLoop.current()
        ioloop.spawn_callback(self._set_gcode_variables)
        ioloop.spawn_callback(self.stop_hyperlapse)

    async def _set_gcode_variables(self) -> None:
        c = self.config
        gcommand = (
            "_SET_TIMELAPSE_SETUP"
            " ENABLE=%(enabled)s"
            " VERBOSE=%(gcode_verbose)s"
            " PARK_ENABLE=%(parkhead)s"
            " PARK_POS=%(parkpos)s"
            " CUSTOM_POS_X=%(park_custom_pos_x)s"
            " CUSTOM_POS_Y=%(park_custom_pos_y)s"
            " CUSTOM_POS_DZ=%(park_custom_pos_dz)s"
            " TRAVEL_SPEED=%(park_travel_speed)s"
            " RETRACT_SPEED=%(park_retract_speed)s"
            " EXTRUDE_SPEED=%(park_extrude_speed)s"
            " RETRACT_DISTANCE=%(park_retract_distance)s"
            " EXTRUDE_DISTANCE=%(park_extrude_distance)s"
            " PARK_TIME=%(park_time)s"
            " FW_RETRACT=%(fw_retract)s"
        ) % c
        logging.debug("timelapse gcode: %s", gcommand)
        try:
            await self.klippy_apis.run_gcode(gcommand)
        except self.server.error:
            logging.exception(
                "timelapse: error executing gcode: %s", gcommand)

    def call_newframe(self, macropark: bool = False,
                      hyperlapse: bool = False) -> None:
        _ = macropark
        if not self.config['enabled']:
            logging.info("timelapse: NEW_FRAME ignored — timelapse disabled")
            return

        if self.config['mode'] == "hyperlapse":
            if not hyperlapse:
                logging.info(
                    "timelapse: ignoring non-hyperlapse frame in hyperlapse mode")
                return
            if self.takingframe:
                logging.info(
                    "timelapse: last frame not yet complete, ignoring")
                return
            self.takingframe = True

        self._spawn_newframe_callbacks()

    def _spawn_newframe_callbacks(self) -> None:
        ioloop = IOLoop.current()
        ioloop.call_later(
            delay=self.config['park_time'],
            callback=self._release_parked_head,
        )
        ioloop.call_later(
            delay=self.config['stream_delay_compensation'],
            callback=self.newframe,
        )

    async def _release_parked_head(self) -> None:
        gcommand = (
            "SET_GCODE_VARIABLE "
            "MACRO=TIMELAPSE_TAKE_FRAME "
            "VARIABLE=takingframe VALUE=False"
        )
        logging.debug("timelapse gcode: %s", gcommand)
        try:
            await self.klippy_apis.run_gcode(gcommand)
        except self.server.error:
            logging.exception(
                "timelapse: error executing gcode: %s", gcommand)

    async def start_hyperlapse(self) -> None:
        hyperlapse_cycle = self.config['hyperlapse_cycle']
        park_time = self.config['park_time']
        if hyperlapse_cycle - park_time < 1:
            logging.info(
                "timelapse: blocked hyperlapse start — cycle (%ss) "
                "too close to park_time (%ss)",
                hyperlapse_cycle, park_time,
            )
            return
        gcommand = "HYPERLAPSE ACTION=START CYCLE=%s" % hyperlapse_cycle
        logging.debug("timelapse gcode: %s", gcommand)
        try:
            await self.klippy_apis.run_gcode(gcommand)
            self.hyperlapserunning = True
        except self.server.error:
            logging.exception(
                "timelapse: error executing gcode: %s", gcommand)

    async def stop_hyperlapse(self) -> None:
        gcommand = "HYPERLAPSE ACTION=STOP"
        logging.debug("timelapse gcode: %s", gcommand)
        try:
            await self.klippy_apis.run_gcode(gcommand)
        except self.server.error:
            logging.exception(
                "timelapse: error executing gcode: %s", gcommand)
        self.hyperlapserunning = False

    async def newframe(self) -> None:
        await self._get_webcam_config()

        self.framecount += 1
        framefile = "frame%s.jpg" % str(self.framecount).zfill(6)
        path = self.temp_dir + framefile
        lastframe_path: Optional[str] = (
            self.temp_dir + self.lastframefile if self.lastframefile else None
        )

        success = False
        for _ in range(3):
            try:
                resp = requests.get(
                    self.config['snapshoturl'], timeout=1.5)
                if resp.status_code == 200:
                    with open(path, "wb") as f:
                        f.write(resp.content)
                    success = True
                    break
            except requests.RequestException:
                pass

        if not success:
            if lastframe_path and os.path.exists(lastframe_path):
                shutil.copy(lastframe_path, path)
                logging.info(
                    "timelapse: fallback frame used for %s", framefile)
            else:
                logging.info(
                    "timelapse: camera unreachable, saving blank frame %s",
                    framefile)
                if _PIL_AVAILABLE:
                    PilImage.new("RGB", (640, 480), (0, 0, 0)).save(path)
                else:
                    logging.warning(
                        "timelapse: Pillow not installed, blank frame skipped")

        self.lastframefile = framefile
        self.notify_event({
            'action': 'newframe',
            'frame': str(self.framecount),
            'framefile': framefile,
            'status': 'success' if success else 'fallback',
        })
        self.takingframe = False

    async def handle_status_update(self, status: Dict[str, Any]) -> None:
        state = status.get('print_stats', {}).get('state')
        if state == 'cancelled':
            self.printing = False
            IOLoop.current().spawn_callback(self.stop_hyperlapse)

    async def handle_gcode_response(self, gresponse: str) -> None:
        ioloop = IOLoop.current()
        if gresponse == "File selected":
            self.cleanup()
            self.printing = True
            if self.config['mode'] == "hyperlapse":
                ioloop.spawn_callback(self.start_hyperlapse)
        elif gresponse == "Done printing file":
            self.printing = False
            if self.config['mode'] == "hyperlapse":
                ioloop.spawn_callback(self.stop_hyperlapse)
            if self.config['enabled']:
                if self.config['saveframes']:
                    ioloop.spawn_callback(self.save_frames_zip)
                if self.config['autorender']:
                    ioloop.spawn_callback(self.render)

    def cleanup(self) -> None:
        logging.debug("timelapse: cleaning frame directory")
        for filepath in glob.glob(self.temp_dir + "frame*.jpg"):
            try:
                os.remove(filepath)
            except OSError as err:
                logging.warning(
                    "timelapse: failed to remove frame: %s", err)
        self.framecount = 0
        self.lastframefile = ""

    def call_save_frames_zip(self) -> None:
        IOLoop.current().spawn_callback(self.save_frames_zip)

    async def save_frames_zip(
            self, webrequest: Optional[WebRequest] = None) -> Dict[str, Any]:
        _ = webrequest
        filelist = sorted(glob.glob(self.temp_dir + "frame*.jpg"))
        self.framecount = len(filelist)
        result: Dict[str, Any] = {'action': 'saveframes'}

        if not filelist:
            result.update({'status': 'skipped', 'msg': 'no frames to save'})
            return result

        if self.saveisrunning:
            result.update({'status': 'running', 'msg': 'save already running'})
            return result

        self.saveisrunning = True
        try:
            kresult = await self.klippy_apis.query_objects(
                {'print_stats': None})
            gcodefilename = (
                kresult.get("print_stats", {})
                       .get("filename", "")
                       .split("/")[-1]
            )
            date_time = datetime.now().strftime(self.config['time_format_code'])
            outfile = "timelapse_%s_%s_frames.zip" % (gcodefilename, date_time)
            outpath = self.out_dir + outfile

            with ZipFile(outpath, "w") as zf:
                for frame in filelist:
                    zf.write(frame, os.path.basename(frame))

            logging.info("timelapse: saved frames to %s", outfile)
            result.update({'status': 'finished', 'zipfile': outfile})
        finally:
            self.saveisrunning = False

        return result

    def call_render(self, byrendermacro: bool = False) -> None:
        self.byrendermacro = byrendermacro
        IOLoop.current().spawn_callback(self.render)

    def _build_filter_param(self) -> str:
        rotation = self.config['rotation']
        flip_x = self.config['flip_x']
        flip_y = self.config['flip_y']

        if rotation == 90 and flip_y:
            return " -vf 'transpose=3'"
        if rotation == 90:
            return " -vf 'transpose=1'"
        if rotation == 180:
            return " -vf 'hflip,vflip'"
        if rotation == 270 and flip_y:
            return " -vf 'transpose=0'"
        if rotation == 270:
            return " -vf 'transpose=2'"
        if rotation > 0:
            rad = rotation * (3.141592653589793 / 180)
            return " -vf 'rotate=%s'" % rad
        if flip_x and flip_y:
            return " -vf 'hflip,vflip'"
        if flip_x:
            return " -vf 'hflip'"
        if flip_y:
            return " -vf 'vflip'"
        return ""

    async def render(
            self, webrequest: Optional[WebRequest] = None) -> Dict[str, Any]:
        _ = webrequest
        filelist = sorted(glob.glob(self.temp_dir + "frame*.jpg"))
        self.framecount = len(filelist)
        result: Dict[str, Any] = {'action': 'render'}

        await self._get_webcam_config()

        if not filelist:
            msg, status = "no frames to render, skip", "skipped"
        elif self.renderisrunning:
            msg, status = "render already running", "running"
        elif not self.ffmpeg_installed:
            msg = "%s not found, please install ffmpeg" % self.ffmpeg_binary_path
            status = "error"
            logging.info("timelapse: %s", msg)
        else:
            self.renderisrunning = True
            try:
                msg, status = await self._do_render(filelist, result)
            finally:
                self.renderisrunning = False

        logging.info("timelapse render: %s", msg)
        result.update({'status': status, 'msg': msg})
        self.notify_event(result)

        if self.byrendermacro:
            gcommand = (
                "SET_GCODE_VARIABLE "
                "MACRO=TIMELAPSE_RENDER VARIABLE=render VALUE=False"
            )
            logging.debug("timelapse gcode: %s", gcommand)
            try:
                await self.klippy_apis.run_gcode(gcommand)
            except self.server.error:
                logging.exception(
                    "timelapse: error executing gcode: %s", gcommand)
            self.byrendermacro = False

        return result

    async def _do_render(
            self,
            filelist: List[str],
            result: Dict[str, Any],
    ) -> Tuple[str, str]:
        kresult = await self.klippy_apis.query_objects({'print_stats': None})
        gcodefilename = (
            kresult.get("print_stats", {})
                   .get("filename", "")
                   .split("/")[-1]
        )

        date_time = datetime.now().strftime(self.config['time_format_code'])
        inputfiles = self.temp_dir + "frame%6d.jpg"
        outfile = "timelapse_%s_%s" % (gcodefilename, date_time)

        duplicates: List[str] = []
        if self.config['duplicatelastframe'] > 0:
            lastframe = filelist[-1]
            for i in range(self.config['duplicatelastframe']):
                nextframe = str(self.framecount + i + 1).zfill(6)
                dup_path = self.temp_dir + "frame%s.jpg" % nextframe
                duplicates.append(dup_path)
                try:
                    shutil.copy(lastframe, dup_path)
                except OSError as err:
                    logging.warning(
                        "timelapse: duplicate last frame failed: %s", err)
            filelist = sorted(glob.glob(self.temp_dir + "frame*.jpg"))
            self.framecount = len(filelist)

        if self.config['variable_fps']:
            fps = int(self.framecount / max(self.config['targetlength'], 1))
            fps = max(
                min(fps, self.config['variable_fps_max']),
                self.config['variable_fps_min'],
            )
        else:
            fps = self.config['output_framerate']

        filter_param = self._build_filter_param()

        cmd = (
            "%(ffmpeg)s"
            " -r %(fps)s"
            " -i '%(input)s'"
            "%(filter)s"
            " -threads 2 -g 5"
            " -crf %(crf)s"
            " -vcodec libx264"
            " -pix_fmt %(pixfmt)s"
            " -an"
            " %(extra)s"
            " '%(output)s' -y"
        ) % {
            'ffmpeg': self.ffmpeg_binary_path,
            'fps': fps,
            'input': inputfiles,
            'filter': filter_param,
            'crf': self.config['constant_rate_factor'],
            'pixfmt': self.config['pixelformat'],
            'extra': self.config['extraoutputparams'],
            'output': self.temp_dir + outfile + ".mp4",
        }

        logging.info("timelapse: starting ffmpeg: %s", cmd)
        result.update({
            'status': 'started',
            'framecount': str(self.framecount),
            'settings': {
                'framerate': fps,
                'crf': self.config['constant_rate_factor'],
                'pixelformat': self.config['pixelformat'],
            },
        })

        shell_cmd: SCMDComp = self.server.lookup_component('shell_command')
        self.notify_event(result)
        scmd = shell_cmd.build_shell_command(cmd, self.ffmpeg_cb)
        cmdstatus = False
        try:
            cmdstatus = await scmd.run(
                verbose=True, log_complete=False, timeout=9999999999)
        except Exception:
            logging.exception("timelapse: error running ffmpeg: %s", cmd)

        if cmdstatus:
            status = "success"
            msg = "rendering successful: %s.mp4" % outfile
            result.pop("settings", None)
            result.update({
                'filename': "%s.mp4" % outfile,
                'printfile': gcodefilename,
            })

            try:
                shutil.move(
                    self.temp_dir + outfile + ".mp4",
                    self.out_dir + outfile + ".mp4",
                )
            except OSError as err:
                logging.warning(
                    "timelapse: moving output file failed: %s", err)

            if self.config['previewimage']:
                preview_file = "%s.jpg" % outfile
                preview_path = self.out_dir + preview_file
                try:
                    shutil.copy(filelist[-1], preview_path)
                except OSError as err:
                    logging.warning(
                        "timelapse: copying preview image failed: %s", err)
                else:
                    result['previewimage'] = preview_file

                if filter_param or self.config['extraoutputparams']:
                    prev_cmd = (
                        "%(ffmpeg)s -i '%(src)s'%(filter)s -an %(extra)s"
                        " '%(dst)s' -y"
                    ) % {
                        'ffmpeg': self.ffmpeg_binary_path,
                        'src': preview_path,
                        'filter': filter_param,
                        'extra': self.config['extraoutputparams'],
                        'dst': preview_path,
                    }
                    logging.info(
                        "timelapse: rotating preview image: %s", prev_cmd)
                    scmd2 = shell_cmd.build_shell_command(prev_cmd)
                    try:
                        await scmd2.run(
                            verbose=True, log_complete=False,
                            timeout=9999999999)
                    except Exception:
                        logging.exception(
                            "timelapse: error rotating preview: %s", prev_cmd)
        else:
            status = "error"
            msg = "rendering failed: %s" % self.lastcmdreponse
            result.update({'cmd': cmd, 'cmdresponse': self.lastcmdreponse})

        for dup in duplicates:
            try:
                os.remove(dup)
            except OSError as err:
                logging.warning(
                    "timelapse: removing duplicate failed: %s", err)

        return msg, status

    def ffmpeg_cb(self, response: bytes) -> None:
        self.lastcmdreponse = response.decode("utf-8")
        match = re.search(r'frame=\s*(\d+)\s+fps', self.lastcmdreponse)
        if not match:
            return
        if self.framecount == 0:
            return
        percent = min(int(int(match.group(1)) / self.framecount * 100), 100)
        if self.lastrenderprogress != percent:
            self.lastrenderprogress = percent
            self.notify_event({
                'action': 'render',
                'status': 'running',
                'progress': percent,
            })

    def notify_event(self, result: Dict[str, Any]) -> None:
        logging.debug("timelapse event: %s", result)
        self.server.send_event("timelapse:timelapse_event", result)


def load_component(config: ConfigHelper) -> Timelapse:
    return Timelapse(config)