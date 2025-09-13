#!/usr/bin/env python3

from __future__ import annotations
import sys, os, re, ssl, time, json, shutil, errno, socket
import platform, subprocess, tempfile, traceback, argparse
import urllib.request
from urllib.error import URLError, HTTPError
from http.client import HTTPResponse
from hashlib import sha256
from typing import Any, Callable, List, Sequence, Tuple, NoReturn, Union, Optional, Dict, IO
from json import JSONDecodeError
from pathlib import Path
from textwrap import dedent
from contextlib import closing
from concurrent.futures import ThreadPoolExecutor, wait, FIRST_COMPLETED

"""
A tool to keep your Minecraft server up to date.
It runs in automated batch or interactive modes, includes built-in SHA-256 integrity checks,
provides robust backup/one-step rollback, and delivers clear,
actionable error messages with suggested fixes for every error.
"""

__version__ = '4.2.1c'


GITHUB = 'https://github.com/Creeper36/PaperMC-Update'
GITHUB_RELEASE = 'https://api.github.com/repos/Creeper36/PaperMC-Update/releases/latest'
GITHUB_RAW = 'https://raw.githubusercontent.com/Creeper36/PaperMC-Update/master/server_update.py'


# === Exit codes (centralized) ===
EXIT_NOTHING     = 0       # Success: nothing to do (already up-to-date)
EXIT_UPDATE      = 1       # Success: Paper update installed
EXIT_UPGRADE     = 2       # Success: Script self-upgrade installed
EXIT_BAD_PY      = 10      # Fatal: Invalid Python version (<3.7)
EXIT_FILE_LOCKED = 11      # Fatal: Target file locked/in use, cannot replace
EXIT_PERM        = 12      # Fatal: Permission denied (write/replace blocked)
EXIT_NOSPACE     = 13      # Fatal: Insufficient disk space during install
EXIT_BAD_PATH    = 14      # Fatal: Invalid path or directory (missing/invalid)
EXIT_BAD_ROOT    = 15      # Fatal: Root directory installs are not allowed
EXIT_INTEGRITY   = 16      # Fatal: Integrity check failed (SHA256 mismatch)
EXIT_NET_DL      = 17      # Fatal: Network download error (HTTP/URL failure)
EXIT_ATOMIC      = 18      # Fatal: Atomic replace failed (unexpected OS error)
EXIT_NET_TIMEOUT = 19      # Fatal: TCP connect timed out (no reply from host)
EXIT_NET_REFUSED = 20      # Fatal: TCP connection refused (port closed)
EXIT_NET_UNREACH = 21      # Fatal: Network unreachable (local routing problem)
EXIT_NET_URL     = 22      # Fatal: Malformed or invalid URL
EXIT_NET_SSL     = 23      # Fatal: SSL handshake or certificate error
EXIT_NET_OFFLINE = 24      # Generic offline fallback (all network tests failed)


def fatal(code: int, message: str = "", target: str = None, os_error: int = None) -> NoReturn:
    """
    Emit a standardized fatal error report and terminate immediately.
    Captures exit code, human-readable context, and optional target path.
    Includes raw OS errno details when provided for deep troubleshooting.
    Guarantees clean process exit with the proper EXIT_* code.
    """
    output("\nx=======================================================================================x\n")
    output("             [ !! FATAL ERROR OCCURRED !! ]")
    output("\nx=======================================================================================x\n")
    if message:
        output(f"     Reason    : {message}")
    output("\nx----------------- ERROR CODE DETAILS --------------------------------------------------x\n")
    if code == EXIT_BAD_PY:
        output(f"  - Target     (current) : {sys.version_info.major}.{sys.version_info.minor}")
        output("  - Expected             : 3.7+")
    else:
        if target:
            output(f"  - Target / Information  : {target}")
        if os_error is not None:
            output(f"  - Python OS Error Code : {os_error}")
    output(f"")
    output(f"  - Script Exit Code      : {code}")
    output("\nx=======================================================================================x\n")
    sys.exit(code)

def error_report(exc, net: bool = False):
    """
    Print raw traceback only. Provides developers with the exact Python error flow.
    """
    a = globals().get("args")

    if a and getattr(a, "quiet", False):

        return

    traceback.print_exc()

    return


if sys.version_info < (3, 7, 0):
    fatal(
        EXIT_BAD_PY,
        f"Invalid Python version detected (current: {sys.version_info.major}.{sys.version_info.minor}).\n\n"
        "     Info      : This updater requires Python 3.7 or newer for compatibility.\n"
        "     Info      : Older Python versions lack required libraries and features.\n"
        "     Fix       : Install Python 3.7+ from https://www.python.org/downloads/.\n"
        "     Fix       : Re-run this updater with the correct interpreter.",
        target=f"(current) : {sys.version_info.major}.{sys.version_info.minor}", os_error=None
    )


filterArray = [
    "[PaperMC", "[ --== Moving", "[ --== Paper", "# Loading build", "# Removed", "# Done",
    "[ --== Checking", "|  ", "[ --== Version", "[ --== Starting", "# Loading version",
    "# Selecting latest", "*****", "+====", "# Temporary", "# Saved"
]



quietmode = any(flag in sys.argv for flag in ("-q", "--quiet"))
"""
Enable global quiet mode if -q/--quiet is present in sys.argv.
Overrides builtins.print and stream writes to suppress all output.
Ensures completely silent operation, including errors and fatals.
Intended for automation where only exit codes are consumed.
"""

if quietmode:

    import builtins

    builtins.print = lambda *a, **k: None

    try:

        sys.stdout.write = lambda *a, **k: None

        sys.stderr.write = lambda *a, **k: None

    except Exception:

        pass


def _errno(e) -> int:
    """
    Safely extract an errno from Python exceptions or wrapped objects.
    Handles OSError, socket errors, and other platforms consistently.
    Returns -1 if no reliable errno can be deduced.
    Ensures downstream error handlers always have a numeric code.
    """

    return getattr(e, "errno", -1)


def _is_enospace(e) -> bool:
    """
    Check if the given exception represents ENOSPC (disk full).
    Works across Python’s different exception classes and OSes.
    Used to distinguish space exhaustion from generic I/O failure.
    Enables targeted EXIT_NOSPACE termination when needed.
    """

    return _errno(e) == errno.ENOSPC


def _is_windows():
    """
    Return True if this process is running on a Windows platform.
    Used to branch file move/rename behavior and ping flags.
    Ensures portability between Windows and POSIX environments.
    A single source of truth for platform-specific logic.
    """

    return platform.system().lower() == "windows"


def scavenge_stale(prefix: str = "pmcupd-"):
    """
    Clean up stale updater artifacts:
      1. Old TemporaryDirectory instances in the system temp folder.
      2. Leftover '.updating' staging files in the server directory
         (derived from args.path, falling back to script location).
    """

    base = Path(tempfile.gettempdir())

    try:

        for p in base.iterdir():

            if p.is_dir() and p.name.startswith(prefix):

                try:

                    shutil.rmtree(p, ignore_errors=True)

                except Exception:

                    pass

    except Exception:

        pass

    try:

        a = globals().get("args")

        if a and getattr(a, "path", None):

            server_dir = Path(a.path).expanduser().resolve()

            if server_dir.is_file():

                server_dir = server_dir.parent

        else:

            server_dir = Path(__file__).expanduser().resolve().parent

        if server_dir.is_dir():

            for f in server_dir.glob("*.updating"):

                try:

                    f.unlink()

                except Exception:

                    pass

    except Exception:

        pass


def check_internet_connection():
    """
    Perform layered connectivity tests: DNS TCP, ICMP ping, and HTTP HEAD.
    Each failure maps to a unique EXIT_* code for diagnostics.
    Succeeds if any probe reaches the Internet within defined timeouts.
    Provides robust classification of offline and transient conditions.
    """

    def _tcp_probe(host: str, port: int, timeout: float = 5.0):
        """
        Attempt a TCP socket connection to the given host/port.
        Returns True on success, False on timeout or error.
        Used as a low-level connectivity check for DNS/Internet reachability.
        """

        try:

            with socket.create_connection((host, port), timeout=timeout):

                return True, None

        except socket.timeout:

            return False, "timeout"

        except OSError as e:

            if getattr(e, "errno", None) == errno.ECONNREFUSED:

                return False, "refused"

            if getattr(e, "errno", None) in (errno.ENETUNREACH, errno.EHOSTUNREACH):

                return False, "unreach"

            return False, "other"


    def _ping_probe(host: str, timeout_s: float = 5.0) -> bool:
        """
        Run a system-level ping to the given host with a timeout.
        Normalizes exit codes across platforms into a boolean result.
        Returns True if the host replies, False otherwise.
        """

        try:

            if _is_windows():

                ms = max(1, int(timeout_s * 1000))

                cmd = ["ping", "-n", "1", "-w", str(ms), host]

            else:

                cmd = ["ping", "-c", "1", "-W", str(int(timeout_s)), host]

            return subprocess.run(cmd, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL).returncode == 0

        except Exception:

            return False


    def _http_head(url: str, timeout: float = 5.0) -> bool:
        """
        Issue a lightweight HTTP HEAD request to the given URL.
        Confirms both network reachability and HTTP server presence.
        Returns True for status <400, False on error or timeout.
        """

        try:

            req = urllib.request.Request(url, method="HEAD")

            with urllib.request.urlopen(req, timeout=timeout):

                return True

        except Exception:

            return False


    def _any_success_bool(tasks):
        """
        Run multiple probe callables and return True if any succeed.
        Short-circuits at the first True result to save time.
        Provides a generic helper for multi-wave connectivity tests.
        """

        if not tasks:

            return False

        with ThreadPoolExecutor(max_workers=len(tasks)) as ex:

            futures = [ex.submit(fn) for fn in tasks]

            while futures:

                done, pending = wait(futures, return_when=FIRST_COMPLETED)

                for d in done:

                    try:

                        if d.result():

                            for p in pending: p.cancel()

                            return True

                    except Exception:

                        pass

                futures = list(pending)

        return False

            # ---------- Wave 1: TCP (fastest) ----------

    tcp_targets = [("1.1.1.1", 53), ("8.8.8.8", 53), ("9.9.9.9", 53)]

    tcp_errors_seen = set()


    def _tcp_task(h, p):
        """
        Run a single TCP probe against host/port.
        Records the specific error kind in tcp_errors_seen if it fails.
        Returns True if the connection succeeded, False otherwise.
        Acts as a thin wrapper around _tcp_probe for error tracking.
        """

        ok, kind = _tcp_probe(h, p, timeout=5.0)

        if not ok and kind:

            tcp_errors_seen.add(kind)

        return ok

    if _any_success_bool([lambda h=h, p=p: _tcp_task(h, p) for (h, p) in tcp_targets]):

        return  # online

            # ---------- Wave 2: ICMP ping ----------

    ping_hosts = ["1.1.1.1", "8.8.8.8", "9.9.9.9"]

    if _any_success_bool([lambda h=h: _ping_probe(h, timeout_s=5.0) for h in ping_hosts]):

        return  # online

            # ---------- Wave 3: HTTP HEAD ----------

    http_urls = ["https://www.google.com/generate_204", "https://1.1.1.1"]

    if _any_success_bool([lambda u=u: _http_head(u, timeout=5.0) for u in http_urls]):

        return  # online

            # ---------- All failed: choose the most informative TCP reason if available ----------

    if "unreach" in tcp_errors_seen:

        fatal(

            EXIT_NET_UNREACH,
            "Network unreachable during URL fetch.\n\n"
            "     Info      : The updater could not reach the target network.\n"
            "     Info      : This can happen if your router, DNS, or ISP is blocking access.\n"
            "     Fix       : Verify your internet settings.\n"
            "     Fix       : Try again after reconnecting to the network.",
            target="network probe"

        )

    if "timeout" in tcp_errors_seen:

        fatal(

            EXIT_NET_TIMEOUT,
            "Network timeout during URL fetch.\n\n"
            "     Info      : The server did not respond in the expected timeframe.\n"
            "     Info      : This usually indicates temporary connectivity issues.\n"
            "     Fix       : Check your internet connection.\n"
            "     Fix       : Retry after a few minutes.",
            target="network probe"

        )

    if "refused" in tcp_errors_seen:

        fatal(

            EXIT_NET_REFUSED,
            "TCP connection refused by host.\n\n"
            "     Info      : The host is reachable, but the target port is closed.\n"
            "     Info      : This may happen if the server is down or blocking requests.\n"
            "     Fix       : Verify that papermc.io is online and accessible.\n"
            "     Fix       : Retry after a few minutes.",
            target="network probe"

        )

    fatal(

        EXIT_NET_OFFLINE,
        "No Internet Connection detected.\n\n"
        "     Info      : The updater was unable to connect using multiple probes.\n"
        "     Info      : TCP, HTTPS, and DNS probes all failed.\n"
        "     Fix       : Check your router and reconnect to the internet.\n"
        "     Fix       : Retry once your network is online.",
        target="network probe"

    )


def human_readable_size(n: int) -> str:
    """
    Convert raw bytes into a formatted human-readable unit string.
    Iteratively scales through KiB, MiB, GiB, etc., up to PiB.
    Rounded to 2 decimals for clarity in user-facing output.
    Primarily used in disk-space checks and status reports.
    """

    units = ["B","KiB","MiB","GiB","TiB","PiB"]

    i = 0

    f = float(n)

    while f >= 1024 and i < len(units)-1:

        f /= 1024.0

        i += 1

    return f"{f:.2f} {units[i]}"


def load_local_version(serv: ServerUpdater) -> Tuple[str, int]:
    """
    Attempt to read the server’s local version_history.json metadata.
    Delegates file handling to FileUtil for safety and normalization.
    Returns (version, build) on success or ('unknown', -1) gracefully.
    Provides a baseline before any remote API queries are made.
    """

    try:

        version, build = serv.fileutil.load_config(serv.config_file)

        return version, build

    except Exception as e:

        output(f"Error loading local version info: {e}")

        return ("unknown", -1)


def load_config_old(config: dict) -> Tuple[str, int]:
    """
    Parse legacy Paper JSON configs in git-style 'git-Paper-<build>'.
    Extracts both MC version and Paper build reliably.
    Maintains backward compatibility for servers on old configs.
    Raises a fatal error if structure is missing or malformed.
    """

    OLD_PREFIX = 'git-Paper'  # Old prefix

    current = config['currentVersion']

    if not OLD_PREFIX == current[:len(OLD_PREFIX)]:

        raise ValueError("Invalid old config data format!")

    build, version = current.split(" ", 1)

    build = int(build.split("-")[-1])

    version = version[5:-1]

    return version, build


def load_config_new(config: dict) -> Tuple[str, int]:
    """
    Parse modern Paper JSON configs where the Paper build may be embedded.
    Extract the Minecraft version and Paper build from 'currentVersion' or
    explicit fields when present. Accept common alias keys and numeric
    strings for the build. Raise ValueError on malformed data so the caller
    can degrade gracefully.
    """

    if not isinstance(config, dict):

        raise ValueError("config is not a dict")

    def pick(d, keys):

        for k in keys:

            if k in d and d[k] not in (None, ""):

                return d[k]

        return None

    ver_str = pick(config, ["currentVersion", "version", "minecraftVersion", "mcVersion"])

    build   = pick(config, ["currentBuild", "build", "buildNumber", "paperBuild"])

    if isinstance(ver_str, str):

        s = ver_str.strip()

        m = re.search(r'(?i)(\d+(?:\.\d+){0,2})-(\d+)(?:-[0-9a-f]{5,40})?(?:\s*\(MC:\s*(\d+(?:\.\d+){0,2})\s*\))?', s)

        if m:

            mc_from_left = m.group(1)

            mc_from_paren = m.group(3)  # may be None

            derived_mc = (mc_from_paren or mc_from_left)

            derived_build = int(m.group(2))

            ver_str = derived_mc

            if build is None:

                build = derived_build

    if isinstance(build, str):

        m2 = re.search(r"\d+", build)

        if m2:

            build = int(m2.group(0))

    if isinstance(ver_str, str):

        ver_str = ver_str.strip() or None

    if not ver_str or not isinstance(build, int) or build < 0:

        raise ValueError("malformed version_history.json (need version+build)")

    return ver_str, build


def upgrade_script(serv: ServerUpdater, force: bool = False):
    """
    Perform a self-upgrade of this updater from GitHub releases.
    Downloads the latest script, verifies its SHA256 hash, and installs.
    On success, exits with EXIT_UPGRADE to prevent double-execution.
    Force mode overrides version checks to always fetch latest.
    """

    req = urllib.request.Request(GITHUB_RELEASE, headers={'Accept': 'application/vnd.github.v3+json'})

    try:

        with urllib.request.urlopen(req, timeout=5.0) as resp:

            data = json.load(resp)

    except URLError as e:

        error_report(e, net=True); return

    except JSONDecodeError as e:

        error_report(e); return

    except Exception as e:

        error_report(e); return

    if not force and data.get('tag_name') == __version__:

        output("# No Upgrade Necessary!\n")

        return

    if force and data.get('tag_name') == __version__:

        output("# Force Script Download")

    else:

        output("# New Version Available!")

    if not args.batch:

        output("\n[ --== Starting Script Upgrade: ==-- ]\n")

    if getattr(sys, 'frozen', False):

        output("# Can't Upgrade Frozen Files!")

        return

    url = GITHUB_RAW

    target_path = Path(__file__).resolve().absolute()

    serv.fileutil.create_temp_dir()

    tmp_file = Path(serv.fileutil.temp.name).expanduser().resolve() / 'server_update.tmp'

    try:
 
        expected_sha = ""

        try:

            sha_url = GITHUB_RAW.rsplit('/', 1)[0] + '/.server_update.py.sha'

            sha_req = urllib.request.Request(sha_url)

            with urllib.request.urlopen(sha_req, timeout=5.0) as sresp:

                text = (sresp.read().decode("utf-8", "replace") or "")

            for tok in text.replace("\r", " ").replace("\n", " ").split():

                t = tok.strip()

                if len(t) == 64 and all(c in "0123456789abcdefABCDEF" for c in t):

                    expected_sha = t.lower()

                    break

        except Exception as e:

            error_report(e, net=isinstance(e, URLError))

            fatal(

                EXIT_INTEGRITY,
                "Missing script SHA256 (required for integrity).\n\n"
                "     Info      : The updater could not verify the integrity of the downloaded script.\n"
                "     Info      : The expected SHA256 hash was not provided by the server.\n"
                "     Fix       : Ensure you are downloading from the official GitHub source.\n"
                "     Fix       : Retry the update later or manually verify the script.",
                target="script upgrade"

            )

        if not expected_sha or len(expected_sha) != 64 or any(c not in "0123456789abcdef" for c in expected_sha):

            fatal(

                EXIT_INTEGRITY,
                "Malformed or missing script SHA256 (required for integrity).\n\n"
                "     Info      : The SHA256 value was missing or not a valid 64-character hex string.\n"
                "     Info      : This may indicate corruption or tampering.\n"
                "     Fix       : Delete the corrupted file and retry.\n"
                "     Fix       : Ensure your internet connection is stable.",
                target="script upgrade"

            )

        output(f"# Remote File Found! -- SHA256 Ending in: {expected_sha[-10:]}")

        if not args.batch:

            output("\n[ --== Starting Download: ==-- ]\n")
        if args.batch:

            output("# Starting Download...")

        req = urllib.request.Request(url)

        with urllib.request.urlopen(req, timeout=15.0) as resp:

            length = resp.length or int(resp.headers.get('Content-Length', 0))

            blocksize = 65536

            total_steps = max(1, (length + blocksize - 1) // blocksize)

            progress_cb = progress_bar if not args.quiet else (lambda *a, **k: None)

            with open(tmp_file, 'wb') as f:

                step = 0

                while True:

                    chunk = resp.read(blocksize)

                    if not chunk:

                        break

                    f.write(chunk)

                    progress_cb(length, blocksize, total_steps, step)

                    step += 1

        actual_sha = sha256(tmp_file.read_bytes()).hexdigest().lower()

        if actual_sha != expected_sha:

            fatal(

                EXIT_INTEGRITY,
                "SHA256 mismatch for script download.\n\n"
                "     Info      : The downloaded file does not match its expected checksum.\n"
                "     Info      : This can happen if the file was corrupted or tampered with.\n"
                "     Fix       : Delete the corrupted file and re-run the updater.\n"
                "     Fix       : Ensure your network connection is stable.",
                target=str(tmp_file), os_error=None

            )

        else:

            output(f"# Integrity Test Passed! -- SHA256 Ending in: {actual_sha[-10:]}")

        output(f"# Saved file to: {tmp_file}")

        if not args.batch:

            output("\n[ --== Download Complete! ==-- ]")

        else:

            output("# Download complete!")

        serv.fileutil.path = target_path

        serv.fileutil.install(tmp_file, target_path)

        if not args.batch:

            output("\n[ --== Script Upgrade Complete! ==-- ]")

        else:

            output("# Script Upgrade Complete!")

        sys.exit(EXIT_UPGRADE)

    finally:

        try:

            if tmp_file.exists():

                try:

                    tmp_file.unlink()

                except IsADirectoryError:

                    shutil.rmtree(tmp_file, ignore_errors=True)

                except Exception:

                    pass

        except Exception:

            pass

        try:

            serv.fileutil.close_temp_dir()

        except Exception:

            pass

        try:

            scavenge_stale()

        except Exception:

            pass


def output(text: str):
    """
    Central logging function aware of batch/quiet flags.
    Routes messages through stdout with optional suppression.
    Filters redundant blank lines for clean console presentation.
    Guarantees consistent user messaging across all modules.
    """

    a = globals().get("args")

    if a and getattr(a, "quiet", False):

        return

    if a and getattr(a, "batch", False):

        if not text.strip():

            return

        for pattern in filterArray:

            if pattern in text:

                return

        print(text.strip())

    else:

        print(text)


def progress_bar(length: int, stepsize: int, total_steps: int, step: int, prefix: str="# Downloading:", size: int=60, prog_char: str="#", empty_char: str="."):
    """
    Render an ASCII progress bar showing download completion.
    Scales proportionally to length and step counters supplied.
    Provides user feedback during long transfers or copies.
    Disabled in quiet/batch modes.
    """

    x = int(size*(step+1)/total_steps)

    # Rendering progress bar:

    if args.quiet or args.batch:

        return

    sys.stdout.write("{}[{}{}] {}/{}\r".format(prefix, prog_char*x, empty_char*(size-x),
                                                        (step*stepsize if step < total_steps - 1 else length), length))
    sys.stdout.flush()

    if step >= total_steps - 1 :

        sys.stdout.write("\n")

        sys.stdout.flush()


class Update:
    """
    PaperMC downloads client with v3 primary and v2 fallback.
    Caches HTTP JSON, builds URLs, and resolves artifacts robustly.
    Normalizes version/build lists across API shapes and schema drift.
    Provides verified, resumable-style downloads via streaming reads.
    """

    def __init__(self, user_agent: str = ''):
        """
        Initialize HTTP bases, default headers, and a local response cache.
        Accepts an optional custom User-Agent to satisfy API policy.
        Prefers v3 endpoints while retaining seamless v2 compatibility.
        Keeps minimal mutable state: base URL, cache, and download path.
        """

        self._base_v3 = 'https://fill.papermc.io/v3/projects/paper'

        self._base_v2 = 'https://api.papermc.io/v2/projects/paper'

        self._base = self._base_v3

        self._headers = {

             'Content-Type': 'application/json;charset=UTF-8',

             'Accept': 'application/json, text/plain, */*',

             'User-Agent': f'PaperMC-Update/{__version__} (https://github.com/Creeper36/PaperMC-Update)',

             'Accept-Language': 'en-US,en;q=0.5',

             'DNT': '1',

        }

        if user_agent:

            self._headers['User-Agent'] = user_agent

        self.download_path = ''

        self.cache = {}


    def _none_function(self, length, blocksize, total, step, *args, **kwargs):
        """
        No-op progress callback used when none is provided by the caller.
        Preserves a stable signature for download hooks and testing.
        Eliminates conditional branches in the hot download loop.
        Safe to call arbitrarily with unused positional/keyword args.
        """

        pass


    def version_convert(self, ver: str) -> Tuple[int,int,int]:
        """
        Convert semantic-like versions into (major, minor, patch) ints.
        Ignores suffixes (pre/rc/+meta) and zero-fills missing parts.
        Enables robust numeric sorting across heterogeneous tags.
        Returns a strict, comparable tuple for downstream selection.
        """

        core = ver.split('-', 1)[0].split('+', 1)[0].strip()

        nums: List[int] = []

        for token in core.split('.'):

            m = re.match(r'(\d+)', token)

            nums.append(int(m.group(1)) if m else 0)

        while len(nums) < 3:

            nums.append(0)

        return (nums[0], nums[1], nums[2])


    def build_data_url(self, version: Optional[str] = None, build_num: Optional[int] = None) -> str:
        """
        Construct the metadata URL for project/version/build resources.
        Root (None,None) yields the project index; deeper paths are nested.
        Stays agnostic to base (v3/v2) so callers can swap transparently.
        Produces clean, slash-joined paths without trailing artifacts.
        """

        final = self._base

        if version is not None:

            final = final + '/versions/' + str(version)

            if build_num is not None:

                final = final + '/builds/' + str(build_num)

        return final


    def build_download_url(self, version: str, build_num: int) -> Dict[str, Any]:
        """
        Read build metadata and select the primary server artifact.
        Prefers 'server:default' but falls back to 'application' when needed.
        Returns a small map: name, url, size, and checksums if available.
        Raises via callers if metadata is missing or malformed.
        """

        downloads = self.decode_json_metadata(version, build_num).get("downloads", {})

        return downloads.get("server:default") or downloads.get("application") or {}

        
    def download_response(self, url: str) -> HTTPResponse:
        """
        Issue a timed HTTP request with strict headers and return the stream.
        Maps recoverable network failures to a unified EXIT_NET_DL fatal.
        Keeps API-specific status handling outside the download path.
        Always returns a live file-like object on success.
        """

        import socket
        
        req = urllib.request.Request(url, headers=self._headers)

        try:

            return urllib.request.urlopen(req, timeout=15.0)

        except ssl.SSLError as e:

            fatal(

                EXIT_NET_SSL,
                "SSL error during file download.\n\n"
                "     Info      : The SSL handshake failed or certificate was invalid.\n"
                "     Fix       : Check your system clock, CA certs, or try again later.\n",
                target=url, os_error=None

            )

        except (HTTPError, URLError, TimeoutError, socket.timeout, ConnectionError) as e:

            error_report(e, net=True)

            fatal(

                EXIT_NET_DL,
                "Network error while downloading Paper jar.\n\n"
                "     Info      : The download failed due to connectivity issues.\n"
                "     Info      : This may be caused by packet loss or server issues.\n"
                "     Fix       : Verify your internet connection.\n"
                "     Fix       : Retry download later.",
                target=url, os_error=None

            )


    def download_file(self, path: Path, version: str, build_num:int, check:bool=True, call: Callable=None, args: List=None, blocksize: int=65536) -> Path:
        """
        Stream an artifact to disk with incremental progress callbacks.
        Honors a fixed block size and computes total steps for UI feedback.
        Optionally verifies SHA-256 and fatals on mismatch for safety.
        Returns the final file path; caller handles post-processing.
        """

        from contextlib import closing

        if args is None:

            args = []

        if call is None:

            call = self._none_function

            args = []

        ddata = self.build_download_url(version, build_num)

        name = str(ddata.get("name", ""))

        expected_hash = str((ddata.get("checksums") or {}).get("sha256", ""))

        url = ddata.get("url") or f"{self.build_data_url(version, build_num)}/downloads/{name}"

        if path.is_dir():

            path = path / name

        length: int = int(ddata.get("size") or 0)

        total_steps = max(1, (length + blocksize - 1) // blocksize)

        with closing(self.download_response(url)) as data, open(path, mode='wb') as file:

            step = 0

            while True:

                chunk = data.read(blocksize)

                if not chunk:

                    break

                file.write(chunk)

                call(length, blocksize, total_steps, step, *args)

                step += 1

        if check:

            checksums = ddata.get("checksums") or {}

            expected = checksums.get("sha256")

            if expected:

                with open(path, "rb") as file:

                    actual = sha256(file.read()).hexdigest()

                if actual.lower() != expected.lower():

                    try:

                        path.unlink()

                    except Exception:

                        pass

                    output("\n" + "="*60)
                    output("###   FATAL ERROR: SHA-256 INTEGRITY CHECK FAILED   ###")
                    output("="*60 + "\n")
                    output(f"Expected: {expected}")
                    output(f"Actual:   {actual}")

                    fatal(

                        EXIT_INTEGRITY,
                        "Integrity verification failed (SHA-256 mismatch).\n\n"
                        "     Info      : The downloaded file’s checksum does not match the expected value.\n"
                        "     Info      : This can happen due to corruption or tampering.\n"
                        "     Fix       : Delete the corrupted file and retry.\n"
                        "     Fix       : Ensure your disk and network connection are stable.",
                        target=str(path), os_error=None

                    )

                output(f"# Integrity Test Passed! -- SHA256 Ending in: {actual[-10:]}")

            else:

                output("# Warning: Integrity Check Skipped (no SHA-256 provided by API)")

        else:

            output("# Integrity Check Skipped (forced: --no-integrity)")

        return path


    def get_versions(self) -> List[str]:
        """
        Fetch project versions and normalize across dict/list schemas.  
        Flattens v3 maps, preserves order, then reverses oldest→newest.
        Guarantees latest is at the end for consistent [-1] selection.
        Caches responses to minimize network churn in repeated calls.
        """

        raw = self.decode_json_metadata().get('versions', [])

        if isinstance(raw, dict):

            out = []

            for _, vals in raw.items():

                out.extend(vals)

            versions = out

        else:

            versions = list(raw)

        versions.reverse()

        return versions


    def get_buildnums(self, version: str) -> List[int]:
        """
        Retrieve integer build numbers for a specific game version.
        Normalizes ordering and reverses so newest is positioned last.
        Ensures max(builds) and builds[-1] converge in typical cases.
        Resilient to sparse or non-contiguous build sequences.
        """

        builds: List[int] = self.decode_json_metadata(version)['builds']

        builds.reverse()

        return builds


    def fetch_raw_api(self, version: Optional[str], build_num: Optional[int]) -> IO[bytes]:
        """
        Attempt v3, then fall back to v2 with a single clear notice.
        Classifies timeouts, HTTP, URL, and connection errors to EXIT_*.
        Returns an open response stream upon first successful attempt.
        Updates self._base to the working endpoint for future calls.
        """

        def try_request(base_url: str):

            url = self.build_data_url(version, build_num).replace(self._base, base_url)

            req = urllib.request.Request(url, headers=self._headers)

            return urllib.request.urlopen(req, timeout=5.0), url

        fallback_noted = False

        for base in [self._base_v3, self._base_v2]:

            try:

                resp, url = try_request(base)

                if base != self._base:

                    self._base = base

                return resp

            except (TimeoutError, socket.timeout):

                if base == self._base_v3:

                    if not fallback_noted:

                        output("# V3 API Failed.. Attempting Fallback to V2 API ..... ")

                        fallback_noted = True

                    continue

                fatal(

                    EXIT_NET_TIMEOUT,
                    "Network timeout during URL fetch.\n\n"
                    "     Info      : The server did not respond in the expected timeframe.\n"
                    "     Info      : This usually indicates temporary connectivity issues.\n"
                    "     Fix       : Check your internet connection.\n"
                    "     Fix       : Retry after a few minutes.",
                    target=base, os_error=None

                )
            
            except HTTPError as e:

                if base == self._base_v3:

                    if not fallback_noted:

                        output("# V3 API Failed.. Attempting Fallback to V2 API ..... ")

                        fallback_noted = True

                    continue  # try v2

                fatal(

                    EXIT_NET_DL,
                    "Connection error during URL fetch.\n\n"
                    "     Info      : The updater attempted to connect but the connection failed.\n"
                    "     Info      : Causes may include firewalls, DNS issues, or server downtime.\n"
                    "     Fix       : Verify papermc.io is reachable from your network.\n"
                    "     Fix       : Retry later or check firewall rules.",
                    target=base, os_error=_errno(e)

                )

            except ssl.SSLError as e:

                fatal(

                    EXIT_NET_SSL,
                    "SSL error during URL fetch.\n\n"
                    "     Info      : A problem occurred during SSL handshake or certificate validation.\n"
                    "     Info      : This may be due to an invalid certificate or outdated system CA.\n"
                    "     Fix       : Check your system clock and ensure certificates are up-to-date.\n"
                    "     Fix       : Retry with a stable network or updated Python/OS.",
                    target=base, os_error=None

                )

            except URLError as e:

                reason = getattr(e, "reason", None)

                eno = _errno(reason) if isinstance(reason, OSError) else _errno(e)

                if eno in (errno.ENETUNREACH, errno.EHOSTUNREACH):

                    fatal(

                        EXIT_NET_UNREACH,
                        "Network unreachable during URL fetch.\n\n"
                        "     Info      : The updater could not reach the target network.\n"
                        "     Info      : This can happen if your router, DNS, or ISP is blocking access.\n"
                        "     Fix       : Verify your internet settings.\n"
                        "     Fix       : Try again after reconnecting to the network.",
                        target=base, os_error=eno

                    )

                if base == self._base_v3:

                    if not fallback_noted:

                        output("# V3 API Failed.. Attempting Fallback to V2 API ..... ")

                        fallback_noted = True

                    continue

                fatal(

                    EXIT_NET_URL,
                    "URL error during URL fetch.\n\n"
                    "     Info      : The provided URL was invalid or inaccessible.\n"
                    "     Info      : A malformed URL or DNS failure may be the cause.\n"
                    "     Fix       : Verify the target URL in your config.\n"
                    "     Fix       : Retry after correcting the URL.",
                    target=base, os_error=eno

                )

            except ConnectionError as e:

                if base == self._base_v3:

                    if not fallback_noted:

                        output("# V3 API Failed.. Attempting Fallback to V2 API ..... ")

                        fallback_noted = True

                    continue

                error_report(e, net=True)

                fatal(

                    EXIT_NET_DL,
                    "Connection error during URL fetch.\n\n"
                    "     Info      : The updater attempted to connect but the connection failed.\n"
                    "     Info      : Causes may include firewalls, DNS issues, or server downtime.\n"
                    "     Fix       : Verify papermc.io is reachable from your network.\n"
                    "     Fix       : Retry later or check firewall rules.",
                    target=base, os_error=_errno(e)

                )

        fatal(

            EXIT_NET_DL,
            "Both v3 and v2 API requests failed.\n\n"
            "     Info      : The updater attempted to query both PaperMC v3 and v2 APIs, but both calls failed.\n"
            "     Info      : This usually indicates a PaperMC server outage or severe connectivity problem.\n"
            "     Fix       : Check https://papermc.io/ for current status.\n"
            "     Fix       : Retry later once the API is available again.",
            target=f"{self._base} and {self._base_v2}", os_error=None

        )


    def decode_json_metadata(self, version: Optional[str] = None, build_num: Optional[int] = None) -> Dict[str, Any]:
        """
        Load and cache project/version/build JSON metadata.
        Uses v2 for root listing; otherwise honors the active base URL.
        Keyed by fully-resolved URL to segregate cache entries correctly.
        Returns a parsed dict ready for selection and download steps.
        """

        if version is None and build_num is None:

            base_url = self._base_v2

        else:

            base_url = self._base

        url = self.build_data_url(version, build_num).replace(self._base, base_url)

        if url in self.cache:

            return self.cache[url]

        with closing(self.fetch_raw_api(version, build_num)) as r:

            data = json.load(r)

        self.cache[url] = data

        return data


class FileUtil:
    """
    Encapsulate filesystem operations for portability and safety.
    Manages temp dirs, config discovery, backups, and atomic moves.
    Abstracts Windows vs POSIX differences in replace semantics.
    Centralizes error handling for clean rollbacks on failure.
    """

    def __init__(self, path, interactive=False):
        """
        Resolve target path, initialize backup state, and flags.
        Interactive mode adjusts messages and certain copy behaviors.
        Accepts files or directories as install destinations.
        Keeps absolute, expanded Paths for consistent downstream use.
        """

        self.path: Path = Path(path).expanduser().resolve().absolute()

        self.temp: tempfile.TemporaryDirectory

        self.config_default: str = 'version_history.json'

        self.target_path: str = ''

        self.interactive: bool = interactive

        self.backup: Optional[Path] = None

        self.backed_up: bool = False


    def create_temp_dir(self):
        """
        Create a dedicated TemporaryDirectory for staging artifacts.
        Stores a handle for later cleanup and backup placement.
        Returns the context so callers can access .name if needed.
        Ensures isolation from the target directory during writes.
        """

        self.temp = tempfile.TemporaryDirectory(prefix="pmcupd-")

        return self.temp

    def close_temp_dir(self):
        """
        Tear down the previously created TemporaryDirectory.
        Frees temporary storage regardless of install outcome.
        Safe to call once after create_temp_dir() completes work.
        No-op if temp dir has already been cleaned up externally.
        """

        try:

            self.temp.cleanup()

        except Exception:

            pass


    def load_config(self, config: str) -> Tuple[str, int]:
        """
        Discover and parse version_history.json with parent fallbacks.
        Supports legacy and modern formats via dedicated parsers.
        Returns ('0', 0) on failure without raising to the caller.
        Emits context messages for traceable resolution steps.
        """

        LAST_FALLBACK_FOLDER_WINDOWS = r"C:\minecraft"

        LAST_FALLBACK_FOLDER_LINUX = Path.home() / "minecraft"

        if config is None:

            if self.path.is_dir():

                config = self.path / self.config_default

            else:

                config = self.path.parent / self.config_default

        output(f"# Loading data from file [{config}] ...")

        if not Path(config).is_file():

            current = Path(config).parent

            found = None

            while current != current.parent:

                candidate = current / Path(config).name

                if candidate.is_file():

                    found = candidate

                    break

                current = current.parent

            if found:

                output(f"# Falling back to [{found}] ...")

                config = found

            else:

                if _is_windows():

                    fallback = Path(LAST_FALLBACK_FOLDER_WINDOWS) / "version_history.json"

                    if fallback.is_file():

                        output(f"# Falling back to [{fallback}] ...")

                        config = fallback

                    else:

                        msg = f"# Unable to load config data from file [{config}] - Not found in any parent directories!"

                        output(msg)

                        if getattr(args, "no_load_config", False):

                            return '0', 0

                        fatal(

                            EXIT_BAD_PATH,
                            "Failed to locate version_history.json and --no-load-config not given.\n\n"
                            "     Info      : The updater could not find a valid configuration file.\n"
                            "     Fix       : Ensure version_history.json exists in the server directory.\n"
                            "     Fix       : Or run with --no-load-config to bypass config loading.",
                            target="version_history.json"

                        )

                else:        # Linux/MacOS

                    fallback = Path(LAST_FALLBACK_FOLDER_LINUX) / "version_history.json"

                    if fallback.is_file():

                        output(f"# Falling back to [{fallback}] ...")

                        config = fallback

                    else:

                        msg = f"# Unable to load config data from file [{config}] - Not found in any parent directories!"

                        output(msg)

                        if getattr(args, "no_load_config", False):

                            return '0', 0

                        fatal(

                            EXIT_BAD_PATH,
                            "Failed to locate version_history.json and --no-load-config not given.\n\n"
                            "     Info      : The updater could not find a valid configuration file.\n"
                            "     Fix       : Ensure version_history.json exists in the server directory.\n"
                            "     Fix       : Or run with --no-load-config to bypass config loading.",
                            target="version_history.json"

                        )

        try:

            with open(config, 'r') as file:

                data = json.load(file)

        except JSONDecodeError:

            output("# Failed to load config data - Not in JSON format!")

            return '0', 0

        try:

            return load_config_old(data)

        except Exception:

            pass

        try:

            return load_config_new(data)

        except Exception:

            output("# Failed to load config data - Strange format, we support official builds only!")

            return '0', 0


    def install(self, file_path: str, new_path: str, target_copy: str=None, backup=True, new=False):
        """
        Install the downloaded jar with backup and rollback support.
        Windows deletes/replaces directly; POSIX uses staged atomics.
        Maps permission, path, and space errors to specific EXIT_* codes.
        Returns True on success; False if rollback recovered the old file.
        """

        output("\n[ --== Moving Files To Target: ==-- ]\n")

        if self.interactive:

            output(f"# Interactive mode: moving as '{self.path.name}'")

        else:

            if target_copy is not None and self.path.is_file():

                output("# Moving old file ...")

                output(f"# ({self.path} > {target_copy})")

                try:

                    shutil.copy(self.path, target_copy)

                except Exception as e:

                    self._fail_install("Old File Move")

                    error_report(e)

            if backup and self.path.is_file() and not new:

                output("# Creating backup of previous file ...")

                self.create_backup()

            final_path = self.path.parent / new_path

            final_path.parent.mkdir(parents=True, exist_ok=True)

            if _is_windows():

                if self.path.is_file():

                    output(f"# Deleting existing file at {self.path} ...")

                    try:
                        os.remove(self.path)

                    except PermissionError as e:

                        if getattr(e, "winerror", None) == 32:

                            fatal(

                                EXIT_FILE_LOCKED,
                                f"Cannot delete '{self.path.name}', it is currently In-Use / Locked.\n\n"
                                "     Info      : Another process is holding this file open.\n"
                                "     Fix       : Stop the Minecraft server and try again.\n"
                                "     Fix       : Restart your PC if the file remains locked."

                            )

                        else:

                            fatal(

                                EXIT_PERM,
                                "Permission denied while writing or replacing a file.\n\n"
                                "     Info      : This occurs when your user account lacks write privileges.\n"
                                "     Info      : On Linux/macOS, files may belong to root or another user.\n"
                                "     Fix       : Run the updater with elevated privileges (Administrator / sudo).\n"
                                "     Fix       : Ensure the target directory is writable by your account.",
                                f"Target: {self.path}"

                            )

                    except Exception as e:

                        self._fail_install("Old File Deletion")

                        error_report(e)

                        try:

                            if self.backed_up and self.backup and Path(self.backup).exists():

                                if self._recover_backup():

                                    output("Rollback successful: old file restored from backup.")

                                    return False

                        except Exception:

                            pass

                        fatal(

                            EXIT_ATOMIC,
                            "Atomic replace failed and rollback unsuccessful.\n\n"
                            "     Info      : The updater attempted to replace the target file, but both main\n"
                            " replace and rollback failed.\n"
                            "     Fix       : Close all processes accessing the file.\n"
                            "     Fix       : Run with elevated permissions and retry.",
                            target=final_path, os_error=None

                        )

                output(f"# Moving download data to target location: {final_path}")

                try:

                    shutil.copyfile(file_path, final_path)

                except PermissionError as e:

                    fatal(

                        EXIT_PERM,
                        "Permission denied while writing or replacing a file.\n\n"
                        "     Info      : This occurs when your user account lacks write privileges.\n"
                        "     Info      : On Linux/macOS, files may belong to root or another user.\n"
                        "     Fix       : Run the updater with elevated privileges (Administrator / sudo).\n"
                        "     Fix       : Ensure the target directory is writable by your account.",
                        target=final_path, os_error=_errno(e)

                    )

                except OSError as e:

                    if _is_enospace(e):

                        fatal(

                            EXIT_NOSPACE,
                            f"Not enough disk space at target '{final_path.parent}'.\n\n"
                            "     Info      : Updates require space for the new JAR plus a backup copy.\n"
                            "     Info      : Temporary files may also consume additional disk space.\n"
                            "     Fix       : Free up at least 1–2 GB on the target drive and retry.",
                            target=final_path, os_error=_errno(e)

                        )

                    elif _errno(e) in (errno.ENOENT, errno.ENOTDIR):

                        fatal(

                            EXIT_BAD_PATH,
                            "Invalid path or directory while moving new file.\n\n"
                            "     Info      : The target path does not exist or is not a directory.\n"
                            "     Fix       : Verify the server folder and file name are correct.",
                            target=final_path, os_error=_errno(e)

                        )

                    else:
                        self._fail_install("Atomic Replace")

                        error_report(e)

                        try:

                            if self.backed_up and self.backup and Path(self.backup).exists():

                                if self._recover_backup():

                                    output("Rollback successful: old file restored from backup.")

                                    return False

                        except Exception:

                            pass

                        fatal(

                            EXIT_ATOMIC,
                            "Atomic replace failed and rollback unsuccessful.\n\n"
                            "     Info      : A rollback was attempted after atomic replace failure, but it also failed.\n"
                            "     Info      : This may leave your server jar in a corrupted state.\n"
                            "     Fix       : Restore from a backup if available.\n"
                            "     Fix       : Ensure permissions and free space are adequate before retrying.",
                            target=final_path, os_error=None

                        )

            else:

                output(f"# Moving download data to target location (staged replace): {final_path}")

                staging = final_path.with_suffix(final_path.suffix + ".updating")

                target_dir = final_path.parent

                try:
                    shutil.copyfile(file_path, staging)

                except PermissionError as e:

                    fatal(

                        EXIT_PERM,
                        "Permission denied while staging new file.\n\n"
                        "     Info      : The updater attempted to write a temporary file but lacked permission.\n"
                        "     Info      : This commonly occurs when the user does not own the directory.\n"
                        "     Fix       : Run as Administrator (Windows) or with sudo (Linux/macOS).\n"
                        "     Fix       : Ensure the staging directory is writable.",
                        target=staging, os_error=_errno(e)

                    )

                except OSError as e:

                    if _is_enospace(e):

                        fatal(

                            EXIT_NOSPACE,
                            f"Not enough disk space at target '{target_dir}'.\n\n"
                            "     Info      : Updates require space for the new JAR plus a backup copy.\n"
                            "     Info      : Temporary files may also consume additional disk space.\n"
                            "     Fix       : Free up at least 1–2 GB of storage on the target drive.\n"
                            "     Fix       : Move or delete large files before retrying.",
                            target=final_path.parent, os_error=_errno(e)

                        )

                    elif _errno(e) in (errno.ENOENT, errno.ENOTDIR):

                        fatal(

                            EXIT_BAD_PATH,
                            "Invalid path or directory while staging new file.\n\n"
                            "     Info      : The temporary staging path could not be created or written to.\n"
                            "     Info      : This usually means the path does not exist or is malformed.\n"
                            "     Fix       : Verify the directory structure exists.\n"
                            "     Fix       : Retry with a valid installation path.",
                            target=staging, os_error=_errno(e)

                        )

                    else:

                        self._fail_install("Staging New File")

                        error_report(e)

                        try:

                            if self.backed_up and self.backup and Path(self.backup).exists():

                                if self._recover_backup():

                                    output("Rollback successful: old file restored from backup.")

                                    return False

                        except Exception:

                            pass

                        fatal(

                            EXIT_ATOMIC,
                            "Atomic replace failed and rollback unsuccessful.\n\n"
                            "     Info      : The updater attempted to atomically replace the target jar, but both replace\n"
                            "                 and rollback operations failed.\n"
                            "     Fix       : Ensure no other processes are locking the file.\n"
                            "     Fix       : Retry with elevated permissions.",
                            target=final_path, os_error=None

                        )

                try:

                    os.replace(staging, final_path)

                except PermissionError as e:

                    fatal(

                        EXIT_PERM,
                        "Permission denied during atomic replace.\n\n"
                        "     Info      : The final replace step was blocked by insufficient privileges.\n"
                        "     Info      : This can happen if the target directory belongs to another user.\n"
                        "     Fix       : Run the updater with Administrator/sudo privileges.\n"
                        "     Fix       : Ensure your account has write access to the directory.",
                        target=final_path, os_error=_errno(e)

                    )

                except OSError as e:

                    if _is_enospace(e):

                        fatal(

                            EXIT_NOSPACE,
                            "Not enough disk space during atomic replace.\n\n"
                            "     Info      : The target disk ran out of space while writing the updated jar.\n"
                            "     Info      : Both the new file and a backup copy require available space.\n"
                            "     Fix       : Free 1–2 GB of space on the drive.\n"
                            "     Fix       : Delete or move large files before retrying.",
                            target=final_path, os_error=_errno(e)

                        )

                    elif _errno(e) in (errno.ENOENT, errno.ENOTDIR):

                        fatal(

                            EXIT_BAD_PATH,
                            "Invalid path or directory during atomic replace.\n\n"
                            "     Info      : The updater attempted to replace the jar but the target directory was invalid.\n"
                            "     Info      : This may occur if the path is malformed or missing.\n"
                            "     Fix       : Ensure the target directory exists.\n"
                            "     Fix       : Retry with a valid installation path.",
                            target=final_path, os_error=_errno(e)

                        )

                    else:

                        self._fail_install("Atomic Replace")

                        error_report(e)

                        try:

                            if self.backed_up and self.backup and Path(self.backup).exists():

                                if self._recover_backup():

                                    output("Rollback successful: old file restored from backup.")

                                    return False

                        except Exception:

                            pass

                        fatal(

                            EXIT_ATOMIC,
                            "Atomic replace failed and rollback unsuccessful.\n\n"
                            "     Info      : A rollback was attempted after atomic replace failure, but it also failed.\n"
                            "     Info      : This may leave your server jar in a corrupted state.\n"
                            "     Fix       : Restore from a backup if available.\n"
                            "     Fix       : Ensure permissions and free space are adequate before retrying.",
                            target=final_path, os_error=None

                        )

        output("# Done moving download data to target location!")

        output("\n[ --== Moving Files Complete! ==-- ]")

        return True


    def create_backup(self) -> Optional[Path]:
        """
        Copy the current jar to a temp location for safe rollback.
        Records the backup path and marks the backup as valid.
        Returns the backup Path or None if the copy fails.
        Emits a status line indicating where the backup resides.
        """

        self.backup = None

        self.backed_up = False

        if not self.path.is_file():

            return None

        if getattr(self, "temp", None) is None:

            self.create_temp_dir()

        backup_path = Path(self.temp.name) / 'backup'

        try:

            shutil.copyfile(self.path, backup_path)

            self.backup = backup_path

            self.backed_up = True

            self.target_path = str(self.path)

            output(f"# Backup created at: {backup_path}")

            return backup_path

        except Exception as e:

            self._fail_install("File Backup")

            error_report(e)

            return None


    def _recover_backup(self):
        """
        Attempt to restore the original jar after install failure.
        Deletes a corrupted target and copies the backup into place.
        Prints step-by-step status, including unrecoverable errors.
        Returns True on success; False if recovery could not complete.
        """

        if not (self.backed_up and self.backup and Path(self.backup).exists()):

            output("# No valid backup available for recovery.")

            return False

        output("\nx=================================================x\n")
        output("\n> !ATTENTION! <")
        output("A failure has occurred during the downloading process.")
        output("I'm sure you can see the error information above.")
        output("This script will attempt to recover your old file.")
        output("If this operation fails, check the github page for more info: "
                   "https://github.com/Creeper36/PaperMC-Update")
        output("# Deleting Corrupted temporary File...")

        try:

            os.remove(self.target_path)

        except FileNotFoundError:

            output("# File not found. Continuing operation...")

        except Exception as e:

            output("# Critical error during recovery process!")
            output("# Displaying error information:")

            error_report(e)

            output("Your previous file could not be recovered.")

            return False

        output(f"# Copying backup file [{self.backup}] to server root directory [{self.path}]...")

        try:

            shutil.copyfile(self.backup, self.path)

        except Exception as e:

            output("# Critical error during recovery process!")
            output("# Displaying error information:")

            error_report(e)

            output("Your previous file could not be recovered.")

            return False

        output("\nRecovery Process Complete!")
        output("Your file has been successfully recovered.")
        output("Please debug the situation, and figure out why the problem occurred,")
        output("Before re-trying the update process.")

        return True


    def _fail_install(self, point):
        """
        Announce an installation failure banner with context.
        Identifies the failing point to aid subsequent debugging.
        Compliments error_report() for full exception visibility.
        Does not terminate; caller decides on rollback or fatal().
        """

        output("\nx=================================================x\n")
        output("> !ATTENTION! <")
        output("An error occurred during the download, and we can not continue.")
        output("We will attempt to recover your previous file (If applicable)")
        output("Fail point: {}".format(point))
        output("Detailed error info below:")

        return


class ServerUpdater:
    """
    High-level orchestrator for selection, download, and install.
    Bridges CLI flags to Update/FileUtil with guardrails and logs.
    Provides interactive and non-interactive flows consistently.
    Surfaces clear status, errors, and exit codes to the user.
    """

    def __init__(self, path, config_file: Optional[str] = None, version='0', build=-1, config=True, prompt=True, integrity=True, user_agent: str = ''):
        """
        Bind target paths, flags, and shared Update/FileUtil instances.
        Accept explicit version/build or defer to config/interactive.
        Supports custom UA and integrity toggles for policy compliance.
        Prepares state for subsequent check/select/download steps.
        """

        self.version = version  # Version of minecraft server we are running

        self.buildnum = build  # Buildnum of the current server

        self.fileutil = FileUtil(path)  # Fileutility instance

        self.prompt = prompt  # Whether to prompt the user for version selection

        self.config_file = config_file  # Name of the config file we pull version info from

        self.integrity = integrity  # Boolean determining if we should run an integrity check

        self.version_install = None  # Version to download

        self.build_install = None  # Build to download

        self.config = config

        self.update = Update(user_agent=user_agent)  # Updater Instance


    def start(self):
        """
        Initialize display values from config or provided overrides.
        Establish defaults used by selection and status routines.
        Output a concise summary of current version/build context.
        Does not perform network access or file mutation here.
        """

        temp_version = '0'

        temp_build = 0

        if args.interactive:

            try:

                temp_version, temp_build = self.fileutil.load_config(self.config_file)

                if self.version == '0' and self.buildnum in (0, -1):

                    self.version, self.buildnum = temp_version, temp_build

            except Exception:

                pass

        if self.config and not args.interactive:

            temp_version, temp_build = self.fileutil.load_config(self.config_file)

        if self.version != '0' or self.buildnum not in (0, -1):

            display_version = self.version

            display_build = self.buildnum

            loaded_from_config_for_display = False

        else:

            display_version = temp_version

            display_build = temp_build

            loaded_from_config_for_display = True

        self.report_version(version=display_version, build=display_build)

        if self.version == '0' and self.buildnum == 0:

            if self.prompt:

                self.version = '0'

                self.buildnum = 0

            else:

                self.version = temp_version

                self.buildnum = temp_build

        return


    def report_version(self, version=None, build=None):
        """
        Print a standardized summary of version/build identifiers.
        Accepts overrides; otherwise uses the updater’s current state.
        Keeps output consistent for logs and human inspection.
        Lightweight helper called by initialization and views.
        """

        v = self.version if version is None else version

        b = self.buildnum if build is None else build

        output("\n# Server Version Information:")

        output("  > Version: [{}]".format(v))

        output("  > Build: [{}]".format(b))


    def view_data(self):
        """
        Present a diagnostic snapshot: local config vs remote artifact.
        Includes API base, latency, size, SHA256, commits, and paths.
        Performs disk-space checks and local JAR introspection.
        Designed for --stats to preflight before any install action.
        """

        def out_i(level: int, text: str = "", _BASE: int = 3, _UNIT: int = 4):
        
            output((" " * (_BASE + _UNIT * level)) + text)

        def section(title: str):

            out_i(0, title)

        out_i(0, "\n[ --== PaperMC Server Stats ==-- ]\n\n")

        try:

            local_version, local_build = self.fileutil.load_config(self.config_file)

        except Exception as e:

            self._url_report("API Fetch Operation")

            error_report(e, net=isinstance(e, URLError))

            local_version, local_build = ("unknown", -1)

        section("\nServer Version (Local Config)")

        out_i(1, f"Version: {local_version}")

        out_i(1, f"Build:   {local_build}")

        cfg_guess = (self.fileutil.path / self.fileutil.config_default) if self.fileutil.path.is_dir() else (self.fileutil.path.parent / self.fileutil.config_default)

        out_i(1, f"Config:  {cfg_guess}")

        api_base = None

        remote_name = None

        remote_sha  = None

        remote_size = None

        remote_time = None

        selected_build = local_build

        commits = []

        newer_version_line = "none"

        latency_ms = None

        try:

            versions = self.update.get_versions()

            if local_version in ("unknown", "0") and versions:

                local_version = versions[-1]  # fallback to newest if unknown, just to proceed

            newest_ver = versions[-1] if versions else None

            if newest_ver and newest_ver != local_version:

                newer_version_line = f"{newest_ver} (you are on {local_version})"

            if not isinstance(local_build, int) or local_build <= 0:

                builds = self.update.get_buildnums(local_version)

                selected_build = max(builds) if builds else -1

            t0 = time.perf_counter()

            data = self.update.decode_json_metadata(local_version, selected_build)

            latency_ms = int((time.perf_counter() - t0) * 1000)

            api_base = self.update._base

            downloads = data.get("downloads", {})

            dflt = downloads.get("server:default") or downloads.get("application", {})

            remote_name = dflt.get("name")

            remote_sha  = (dflt.get("checksums") or {}).get("sha256")

            remote_size = int(dflt.get("size") or 0)        

            remote_time = data.get('time', 'unknown')

            commits = data.get("commits") or data.get("changes", []) or []

            builds_for_status = self.update.get_buildnums(local_version)

            latest_build = max(builds_for_status) if builds_for_status else selected_build

            if isinstance(local_build, int) and local_build >= latest_build:

                status_line = "UP-TO-DATE"

            else:

                behind = (latest_build - (local_build if isinstance(local_build, int) else 0)) if (isinstance(latest_build, int) and isinstance(local_build, int) and local_build > 0) else "unknown"

                status_line = f"BEHIND (latest build: {latest_build}, behind by {behind})"

            section("\nUpdate Status")

            out_i(1, f"Current: {status_line}")

            out_i(1, f"Newer game version: {newer_version_line}")

            section("\nRemote Artifact (PaperMC)")

            out_i(1, f"Project: paper   API: {api_base}")

            if latency_ms is not None:

                out_i(1, f"API latency: {latency_ms} ms")

            latest_tag = " (latest)" if (selected_build != local_build and selected_build != -1 and selected_build == latest_build) else ""

            out_i(1, f"Version/Build: {local_version} / {selected_build}{latest_tag}")

            out_i(1, f"File: {remote_name}")

            out_i(1, f"Created: {remote_time}")

            out_i(1, f"Size: { (remote_size or 0) / (1024*1024):.2f} MiB")

            out_i(1, f"SHA256: {remote_sha}")

            if commits:

                section("\nRecent Commits (top 5)")

                for i, c in enumerate(commits[:5], 1):

                    sha7 = c.get("sha") or c.get("commit", "")

                    sha7 = sha7[:7]

                    ctime = c.get("time", "?")

                    summary = c.get("summary") or c.get("message", "")

                    msg = (summary or "").strip().splitlines()[0]

                    out_i(1, f"{i}) {sha7}  {ctime}  {msg}")

        except Exception as e:

            self._url_report("API Fetch Operation")

            error_report(e, net=isinstance(e, URLError))

        section("\nPaths & Space (Preview)")

        tmp_preview = Path(tempfile.gettempdir()) / f"paper_update_tmp"

        out_i(1, f"Temp dir:   {tmp_preview}")

        target_dir = self.fileutil.path if self.fileutil.path.is_dir() else self.fileutil.path.parent

        out_i(1, f"Target dir: {target_dir}")

        if args.output:

            target_file = (target_dir / args.output)

        elif self.fileutil.path.is_file():

            target_file = self.fileutil.path

        else:

            target_file = (target_dir / (remote_name if remote_name else "paper.jar"))

        out_i(1, f"Target file: {target_file}   (--output honored)")

        try:

            du = shutil.disk_usage(str(target_dir))

            free_gib, total_gib = du.free/(1024**3), du.total/(1024**3)

            out_i(1, f"Disk free @ target: {free_gib:.1f} GiB free / {total_gib:.1f} GiB total")

            need = (remote_size or 0) * 2   # Require 2x buffer (new + backup)

            if du.free < need:

                fatal(

                    EXIT_NOSPACE,
                    f"Insufficient disk space at {target_dir}. "
                    f"Free: {human_readable_size(du.free)}, "
                    f"Need: {human_readable_size(need)}",
                    target=str(target_dir)

                )

            else:

                out_i(1, f"Space check: need ~{((remote_size or 0)/(1024*1024)):.2f} MiB "

                         f"(buffer x2 = {(need/(1024*1024)):.2f} MiB) → OK")

        except Exception:

            pass

        writable = os.access(str(target_dir), os.W_OK)

        out_i(1, f"Writable: {'YES' if writable else 'NO'}")

        section("\nLocal File (Actual)")

        jar_path = None

        try:

            if args.path.is_file():

                jar_path = args.path

            elif args.path.is_dir():

                candidate = (args.path / remote_name) if remote_name else None

                if candidate and candidate.is_file():

                    jar_path = candidate

                else:

                    jars = sorted((p for p in args.path.glob('*.jar')), key=lambda p: p.stat().st_mtime, reverse=True)

                    paper_jars = [p for p in jars if p.name.lower().startswith("paper-")]

                    jar_path = (paper_jars[0] if paper_jars else (jars[0] if jars else None))

            if jar_path and jar_path.is_file():

                with open(jar_path, "rb") as f:

                    local_sha = sha256(f.read()).hexdigest()

                st = jar_path.stat()

                import datetime as _dt

                out_i(1, f"Path:  {jar_path}")

                out_i(1, f"Size:  {st.st_size/(1024*1024):.2f} MiB")

                out_i(1, f"MTime: {_dt.datetime.fromtimestamp(st.st_mtime).strftime('%Y-%m-%d %H:%M:%S')}")

                out_i(1, f"SHA256: {local_sha}")

                if remote_sha:

                    note = "MATCH" if local_sha.lower() == remote_sha.lower() else "MISMATCH"

                    out_i(1, f"Compare: local vs remote SHA: {note}")

                    if remote_size:

                        delta = (st.st_size - remote_size)/(1024*1024)

                        out_i(1, f"Size delta: {delta:+.2f} MiB")

            else:

                out_i(1, "Local file not found; unable to compute SHA256.")

        except Exception as e:

            error_report(e)

        section("\nPlugins Snapshot")

        try:

            plug_dir = (args.path if args.path.is_dir() else args.path.parent) / "plugins"

            if plug_dir.is_dir():

                plugs = sorted([p.name for p in plug_dir.glob("*.jar")])

                out_i(1, f"Count: {len(plugs)}")

                if plugs:

                    display = ", ".join(plugs[:7]) + ("..." if len(plugs) > 7 else "")

                    out_i(1, display)

            else:

                out_i(1, "No plugins directory found.")

        except Exception:

            pass

        section("\nEnvironment")

        try:

            out_i(1, f"OS: {platform.system()} {platform.release()}")

            out_i(1, f"Python: {platform.python_version()} ({platform.machine()})")

            ua = self.update._headers.get('User-Agent', '')

            if ua: out_i(1, f"HTTP UA: {ua}")

            import shutil as _sh

            java_path = _sh.which("java")

            if java_path:

                try:

                    proc = subprocess.run(["java", "-version"], capture_output=True, text=True)

                    jver = (proc.stderr or proc.stdout).strip().splitlines()[0]

                    out_i(1, f"Java: {jver}")

                except Exception:

                    pass

            s = socket.socket(socket.AF_INET, socket.SOCK_STREAM)

            s.settimeout(5.0)

            try:

                s.connect(("127.0.0.1", 25565))

                out_i(1, "Port 25565 (localhost): OPEN")

            except Exception:

                out_i(1, "Port 25565 (localhost): closed")

            finally:

                try: s.close()

                except Exception: pass

        except Exception:

            pass

        output("\n\n+===================================END-OF-STATS===================================+\n\n")


    def check(self, default_version: str, default_build: int):
        """
        Compare local state to remote latest and report deltas.
        Evaluates both version and build, handling unknown locals.
        Returns True if an update is available, False otherwise.
        Gracefully maps API failures to error reporting without fatal().
        """

        output("\n[ --== Checking For New Version: ==-- ]\n")

        output("# Loading version information ...")

        try:

            ver = self.update.get_versions()

        except URLError as e:

            self._url_report("API Fetch Operation")

            error_report(e, net=True)

            return False

        except Exception as e:

            self._url_report("API Fetch Operation")

            error_report(e)

            return False

        output("# Comparing local <> remote versions ...")

        if self.version != self._select(default_version, ver, 'latest', 'version', print_output=False) and (self.version == '0' or ver[-1] != self.version):

            output("# New Version available! - [Version: {}]".format(ver[-1]))
            output("\n[ --== Version Check Complete! ==-- ]")

            return True

        output("# No new version available.")
        output("# Loading build information ...")

        builds = []

        try:

            builds = self.update.get_buildnums(self.version)

        except URLError as e:

            self._url_report("File Download")

            error_report(e, net=True)

            return False

        except Exception as e:

            self._url_report("File Download")

            error_report(e)

            return False

        output("# Comparing local <> remote builds ...")

        if builds and self.buildnum != self._select(default_build, builds, 'latest', 'buildnum', print_output=False) and (self.buildnum == 0 or builds[-1] != self.buildnum):

            output("# New build available! - [Build: {}]".format(builds[-1]))
            output("\n[ --== Version Check Complete! ==-- ]")

            return True

        output("# No new build available.")
        output("\n[ --== Version Check Complete! ==-- ]\n")

        return False


    def version_select(self, default_version: str='latest', default_build: int=-1) -> Tuple[str, int]:
        """
        Resolve a concrete (version, build) from flags, config, or input.
        Supports interactive prompts or silent defaults for automation.
        Validates availability and returns normalized types (str,int).
        Non-fatal error paths return ('', -1) to stop safely.
        """

        if self.version_install is not None and self.build_install is not None:

            return self.version_install, self.build_install

        output("\n[ --== Version Selection: ==-- ]\n")

        new_default = str(default_build)

        if new_default == '-1':

            new_default: str = 'latest'

        if not self.prompt:

            output("# Loading version information ...")
        
        try:

            versions = self.update.get_versions()

        except URLError as e:

            self._url_report("API Fetch Operation")

            error_report(e, net=True)

            return '', -1

        except Exception as e:

            self._url_report("API Fetch Operation")

            error_report(e)

            return '', -1

        if self.prompt:

            output("Please enter the version you would like to download:")
            output("Example: 1.4.4")
            output("(Tip: <DEFAULT> Option Is Enclosed In Angle Brackets <>. Press <ENTER> to accept it.)")
            output("(Tip: Enter 'latest' to select the most recent version of paper.)")

            output("\nAvailable versions:")

            for i in versions:

                output("  Version: [{}]".format(i))

            while True:

                ver = input("\nENTER VERSION (press Enter for latest available) <{}>: ".format(default_version))

                ver = self._select(ver, versions, default_version, "version")

                if ver:

                    break

        else:

            ver = self._select('', versions, default_version, "version")

            if not ver:

                output("\n# Aborting download!")

                return '', -1

        output("# Loading build information ...")

        try:

            nums = list(self.update.get_buildnums(ver))

        except URLError as e:

            self._url_report("API Fetch Operation")

            error_report(e, net=True)

            return '', -1

        except Exception as e:

            self._url_report("API Fetch Operation")

            error_report(e)

            return '', -1

        if len(nums) == 0:
            
            output("# No builds available!")
            output("\nThe version you have selected has no builds available.")
            output("This could be because the version you are attempting to download is too new or old.")
            output("The best solution is to either wait for a build to be produced for your version,")
            output("Or select a different version instead.")

            output("\nTo see if a specific version has builds, you can issue the following command:\n")
            output("python server_update.py -nc --version [version]")
            output("\nSimply replace [version] with the version you wish to check.")
            output("This message will appear again if there are still no builds available.")
            output("The script will now exit.")

            return '', -1

        if self.prompt:

            output("\nPlease enter the build you would like to download:")
            output("Example: 205")
            output("(Tip: <DEFAULT> Option Is Enclosed In Angle Brackets <>. Press <ENTER> to accept it.)")
            output("(Tip: Enter 'latest' to select the most recent build of paper.)")

            output("\nAvailable Builds:")

            new = []

            for i in sorted(nums, key=int):

                output("  > Build Num: [{}]".format(i))

                new.append(str(i))

            while True:

                build = input("\nENTER BUILD (press Enter for latest available) <{}>: ".format(new_default))


                build = self._select(build, new, new_default, "build")

                if build:
 
                    break

        else:

            build = self._select('', nums, new_default, "build")

            if not build:

                output("# Aborting download!")

                return '', -1

        output("\n# Selection made:")
        output("   > Version: [{}]".format(ver))
        output("   > Build: [{}]".format(build))

        output("\n[ --== Version Selection Complete! ==-- ]\n")

        self.version_install = str(ver)

        self.build_install = int(build)

        return self.version_install, self.build_install

    def get_new(self, default_version: str='latest', default_build: int=-1, backup: bool=True, new: bool=False, 
            target_copy: str=None, output_name: str=None):
        """
        Download, verify, and install the selected Paper artifact.
        Honors backup/rename settings and integrity verification.
        Emits user-friendly progress and completes with a clear status.
        Updates internal version/build on success and returns truthy.
        """

        ver, build = self.version_select(default_version=default_version, default_build=default_build)

        if ver == '' or build == -1:

            return

        if self.prompt:

            output("\n# Do you want to continue with the download?")

            inp = input("#  (Y/N):").lower()

            if inp in ['n', 'no']:

                output("\nCanceling download...\n")

                return


        try:

            data = self.update.decode_json_metadata(ver, build)

        except Exception as e:

            self._url_report("API Fetch Operation")

            error_report(e, net=isinstance(e, URLError))

            return False

        downloads = data.get("downloads", {})

        dflt = downloads.get("server:default") or downloads.get("application", {})

        expected_hash = str((dflt.get("checksums") or {}).get("sha256", ""))

        if expected_hash:

            eh = expected_hash.lower()

            if len(eh) != 64 or any(c not in "0123456789abcdef" for c in eh):

                fatal(

                    EXIT_INTEGRITY,
                    "Malformed SHA-256 from API (must be 64 hex chars).\n\n"
                    "     Info      : The PaperMC API returned a SHA-256 value that is not valid.\n"
                    "     Info      : This is usually a server-side API bug or corrupted metadata.\n"
                    "     Fix       : Retry later once the API metadata has been corrected.\n"
                    "     Fix       : Report the issue if it persists at https://papermc.io/.",

                )

            if args.interactive:

                output("")

            output(f"# Remote File Found! -- SHA256 Ending in: {expected_hash[-10:]}")

        output("# Creating temporary directory...")

        self.fileutil.create_temp_dir()

        output("# Temporary directory created at: {}".format(self.fileutil.temp.name))

        if not args.batch:

            output("\n[ --== Starting Download: ==-- ]\n")

        if args.batch:

            output("# Starting Download...")

        try:

            path = self.update.download_file(Path(self.fileutil.temp.name), ver, build_num=build, call=progress_bar, check=self.integrity)

        except URLError as e:

            self._url_report("File Download")

            error_report(e, net=True)

            fatal(

                EXIT_NET_DL,
                "Network error while downloading Paper jar.\n\n"
                "     Info      : The updater attempted to download the latest Paper jar but the transfer failed.\n"
                "     Info      : Causes may include timeouts, dropped connections, or server-side issues.\n"
                "     Fix       : Verify your internet connection is stable.\n"
                "     Fix       : Retry later, or check if PaperMC servers are experiencing downtime.",
                target=str(self.fileutil.path), os_error=None

            )


        except Exception as e:

            self._url_report("File Download")

            error_report(e)

            return False

        output("# Saved file to: {}".format(path))

        if not args.batch:

            output("\n[ --== Download Complete! ==-- ]")

        if args.batch:

            output("# Download Complete!")

        target = self.fileutil.path

        if self.fileutil.path.is_dir():

            if output_name:

                target = self.fileutil.path / output_name

            else:

                target = self.fileutil.path / f"paper-{ver}-{build}.jar"

        elif self.fileutil.path.exists() and self.fileutil.path.is_file() and self.fileutil.path.suffix.lower() == ".jar":

            target = self.fileutil.path

        elif not self.fileutil.path.exists() and output_name is None:

            if not self.fileutil.path.parent.exists():

                fatal(

                    EXIT_BAD_PATH,
                    f"Invalid target path: '{self.fileutil.path}'.\n\n"
                    "     Info      : The folder does not exist, the path string is malformed, or the location is not writable.\n"
                    "     Info      : This error often happens if you misspell the directory name, or pass only a filename without a folder.\n"
                    "     Fix       : Create the folder manually before running the updater.\n"
                    "     Fix       : Use -o [filename] if you want to name the output jar explicitly inside an existing folder.\n"

                )

            if self.fileutil.path.parent == Path(self.fileutil.path.anchor):

                fatal(

                    EXIT_BAD_ROOT,
                    f"Root directory installs are not allowed: '{self.fileutil.path}'.\n\n"
                    "     Info      : Installing directly into the root of a drive (C:\\ on Windows, / on Linux/Unix) is unsafe.\n"
                    "     Info      : Backups and rollbacks cannot be managed properly at root, and permission errors are very likely.\n"
                    "     Fix       : Always choose a subfolder dedicated to Minecraft (e.g., C:\\Minecraft\\ or ~/minecraft/).\n"
                    "     Fix       : Move your server files into a proper folder and re-run the updater.\n"

                )

            target = self.fileutil.path

        elif output_name:

            target = self.fileutil.path.parent / output_name

        else:

            fatal(

                EXIT_BAD_PATH,
                f"Invalid target path '{self.fileutil.path}'.\n\n"
                "     Info      : The updater was given a path that is not valid.\n"
                "     Info      : The path must either be a directory or end in .jar.\n"
                "     Fix       : Ensure the folder exists and is writable.\n"
                "     Fix       : Use -o [filename] to set a custom jar name if needed.",
                target=str(self.fileutil.path), os_error=None

            )

        val = self.fileutil.install(path, target, backup=backup, new=new, target_copy=target_copy)

        if not val:

            return

        output("\n# Cleaning Up Temporary Directory...")

        self.fileutil.close_temp_dir()

        output("# Done Cleaning Temporary Directory!")

        output("\n# Update Complete!\n")

        self.version = ver

        self.buildnum = build

        return val


    def _select(self, val, choice, default, name, print_output=True):
        """
        Normalize “latest/current/value” against a candidate list.
        Coerces types, validates membership, and logs selections.
        Supports numeric and string lists for builds and versions.
        Returns the chosen value or None on invalid input.
        """

        if val == '':

            val = default

        if val == -1:

            val = 'latest'

        if isinstance(val, str):

            s = val.strip().lower()

            if s == 'latest':

                val = 'latest'

            elif s == 'current':

                val = 'current'

            else:

                if choice and isinstance(choice[0], int) and s.isdigit():

                    val = int(s)

        if val == 'latest':

            if not choice:

                if print_output:

                    output(f"\n# Error: No {name}s available!")

                return None

            if name in ('build', 'buildnum'):

                if isinstance(choice[0], str):

                    try:

                        nums = [int(x) for x in choice]

                    except ValueError:

                        latest = choice[-1]

                    else:

                        latest = max(nums)

                else:

                    latest = max(choice)

                if print_output:

                    output(f"\n# Selecting latest {name} - [{latest}] ...")

                return latest

            latest = choice[-1]

            if print_output:

                output(f"\n# Selecting latest {name} - [{latest}] ...")

            return latest

        if val == 'current':

            if name == 'version':

                val = self.version

            elif name in ('build', 'buildnum'):

                val = self.buildnum

        if choice:

            if isinstance(choice[0], int) and isinstance(val, str) and val.isdigit():

                val = int(val)

            elif isinstance(choice[0], str) and not isinstance(val, str):

                val = str(val)

        if val not in choice:

            if print_output:

                output(f"\n# Error: Invalid {name} selected!")

            return None

        if print_output:

            output(f"# Selecting {name}: [{val}] ...")

        return val


    def _url_report(self, point: str):
        """
        Print a concise header identifying the failing API stage.
        Associates subsequent tracebacks with the intended operation.
        Improves readability of logs in batch runs.
        Used immediately before error_report() calls.
        """

        output("\nx=================================================x\n")
        output("> !ATTENTION! >")
        output("An error occurred during a request operation.")
        output(f"Fail Point: {point}")
        output("Your check/update operation will be canceled.")
        output("Detailed error info below:")


if __name__ == '__main__':

    scavenge_stale()    

    linesep = os.linesep

    parser = argparse.ArgumentParser(description=r'PaperMC Server Updater -- Typical Syntax: Python C:\minecraft\server_update.py -options C:\minecraft\paper.jar  -- should always end with paper.jar')
    
    parser.add_argument('path', help='Path to paper jar file', default=Path(__file__).expanduser().resolve().absolute().parent, type=Path, nargs='?')
    parser.add_argument('-v', '--version', help='[##.##.##] Manually set a server version to download (Sets default value)', default='latest', type=str)
    parser.add_argument('-b', '--build', help='[###] Manually set a build number to download (Sets default value)', default=-1, type=int)
    parser.add_argument('-sv', '--server-version', help="Displays the current paper server version from version-history.json.", action='store_true')
    parser.add_argument("-V", "--script-version", help="Display this scripts version and basic contact info", action="store_true")
    parser.add_argument('-s', '--stats', help='Displays statistics on the whole system', action='store_true')
    parser.add_argument('-c', '--check-only', help='Checks for an update, does not download', action='store_true')
    parser.add_argument('-i', '--interactive', help='Prompts the user for the paper.jar version they would like to download', action='store_true')
    parser.add_argument("-ua", "--user-agent", help="User agent to utilize when making requests this should be unique and custom to you! See https://mdn.io/user-agent for additional help", type=str, default='')
    parser.add_argument('-n', '--new', help='Downloads a new paper jar - like --no-check but deals more with names and folders', action='store_true')
    parser.add_argument('-nb', '--no-backup', help='Disables backup of the old server jar', action='store_true')
    parser.add_argument('-ni', '--no-integrity', help='DISABLES SHA-256 verification of downloads. USE WITH CAUTION!', action='store_false')
    parser.add_argument('-nc', '--no-check', help='Does not check for an update - like --new but deals more with numbers and version decision making', action='store_true')
    parser.add_argument('-o', '--output', help='Specify unique output filenames even with alternate extensions')
    parser.add_argument('-co', '--copy-old', help='Copies the old jar file to a new location')
    parser.add_argument('-cf', '--config-file', help='Path to version_history.json - Defaults to Server JAR Folder (has many fallback searches')
    parser.add_argument('-nlc', '--no-load-config', help='Skip loading version_history.json', action='store_true', default=False)
    parser.add_argument('-ba', '--batch', help='Log-friendly output mainly for batch scripts', action='store_true')
    parser.add_argument('-q', '--quiet', help="Suppress all output! -silent mode- Only exit codes will be returned.", action='store_true')
    parser.add_argument('-u', '--upgrade', help='Upgrades this script to a new version if necessary, and exits', action='store_true')
    parser.add_argument('-F', '--force-upgrade', help='Force a script upgrade even if versions match (implies --upgrade)', action='store_true')
    rare = parser.add_argument_group('Rare Options', 'Arguments usually only used by devs or advanced users')
    rare.add_argument('-iv', help='Sets the currently installed server version, ignores version_history.json', default='0', type=str)
    rare.add_argument('-ib', help='Sets the currently installed server build number, ignores version_history.json', default=0, type=int)

    args = parser.parse_args()

    def _bind_output_with_args(_args):
        """
        Bind the global output() to current CLI flags and filters.
        Provides a stable logging surface across the codebase.
        Keeps presentation concerns decoupled from business logic.
        Must be invoked once after argparse has parsed flags.
        """

        global output

        _orig_output = output

        def _bound_output(text, args=None):
            """
            Wrapped output implementation honoring batch/quiet modes.
            Filters noisy lines and preserves essential diagnostics.
            Provides a single choke point for user-visible messages.
            Internal helper; not intended for direct external use.
            """

            return _orig_output(text)

        output = _bound_output

    _bind_output_with_args(args)
    
    check_internet_connection()

if args.stats or args.check_only or getattr(args, "server_version", False):

    p = getattr(args, "path", None)

    if p is not None and not Path(p).expanduser().exists():

        fatal(
            EXIT_BAD_PATH,
            "Operator supplied a path that does not exist for this read-only command.\n"
            "     Info : For --stats/--check-only/--server-version we do not auto-resolve.\n"
            "     Fix  : Correct the path or point to a valid server directory/JAR.",
            target=str(p),

        )

if args.server_version:

    if not args.path or args.path.is_dir():

        fatal(

            EXIT_BAD_PATH,
            "You must provide a .jar file when using --server-version.\n\n"
            "     Info      : The updater expected a server JAR as the last argument.\n"
            "     Fix       : Example: python server_update.py -sv C:\\minecraft\\paper.jar",
            target=str(args.path) if args.path else None,
            os_error=None

        )   

if not (args.batch):

    output("\n+==========================================================================+")
    banner = dedent(r'''
            |     _____                              __  __          __      __        |
            |    / ___/___  ______   _____  _____   / / / /___  ____/ /___ _/ /____    |
            |    \__ \/ _ \/ ___/ | / / _ \/ ___/  / / / / __ \/ __  / __ `/ __/ _ \   |
            |   ___/ /  __/ /   | |/ /  __/ /     / /_/ / /_/ / /_/ / /_/ / /_/  __/   |
            |  /____/\___/_/    |___/\___/_/      \____/ .___/\__,_/\__,_/\__/\___/    |
            |                                         /_/                              |''').lstrip('\n')
    output(banner)
    output("+==========================================================================+")
    output("\n[PaperMC Server Updater]")
    output("[Handles the checking, downloading, and updating of server versions]")
    output("[Written by: Owen Cochell and Creeper36]\n")

serv = ServerUpdater(args.path, config_file=args.config_file, config=(not args.no_load_config), prompt=args.interactive, version=args.iv, build=args.ib, integrity=args.no_integrity, user_agent=args.user_agent)

update_available = True

if args.check_only:

    output("\n[ --== Checking For New Version: ==-- ]\n")

    local_version, local_build = serv.fileutil.load_config(serv.config_file)

    output("\n+=================================================+")
    output("# Local Server Version Information:")
    output(f"  > Version: [{local_version}]")
    output(f"  > Build:   [{local_build}]")
    output("+=================================================+")

    try:

        remote_builds = serv.update.get_buildnums(local_version)

    except Exception as e:

        error_report(e, net=isinstance(e, URLError))

        sys.exit(EXIT_NOTHING)

    if not remote_builds:

        output(f"No builds found for version {local_version}")

        sys.exit(EXIT_NOTHING)

    latest_remote_build = max(remote_builds)

    output("\n+=================================================+")
    output("# Remote Server Version Information:")
    output(f"  > Version: [{local_version}]")
    output(f"  > Build:   [{latest_remote_build}]")
    output("+=================================================+\n")

    if local_build >= latest_remote_build:

        output("# You are up to date!")

    else:

        output(f"# New Version Available! - [Version: {local_version}-{latest_remote_build}]")

    output("\n[ --== Version Check Complete! ==-- ]")

    if args.check_only:

                output("")   # Keep for spacing alignment

    sys.exit(EXIT_NOTHING)

if args.force_upgrade:

    output("# Force Script Upgrade! (forced: -F)\n")

if args.upgrade or args.force_upgrade:

    output("# Checking For Script Upgrade ...")

    upgrade_script(serv, force=args.force_upgrade)

    sys.exit(EXIT_NOTHING)

if args.server_version:

    try:

        try:

            local_version, local_build = serv.fileutil.load_config(serv.config_file)

        except Exception as e:

            serv._url_report("Load Local Config")

            error_report(e)

            local_version, local_build = ("unknown", -1)

        jar_path = None

        base_dir = args.path if args.path.is_dir() else args.path.parent

        if args.path.is_file() and args.path.suffix.lower() == ".jar":
            jar_path = args.path

        else:

            jars = sorted((p for p in base_dir.glob("*.jar")),

                          key=lambda p: p.stat().st_mtime,

                          reverse=True)

            paper_jars = [p for p in jars if p.name.lower().startswith("paper-")]

            jar_path = paper_jars[0] if paper_jars else (jars[0] if jars else None)

        if jar_path and jar_path.is_file():

            try:

                with open(jar_path, "rb") as f:

                    local_sha = sha256(f.read()).hexdigest()

                local_sha_line = f"  > SHA256:  [{local_sha}]"

            except Exception as e:

                error_report(e)

                local_sha_line = "  > SHA256:  [Error reading file]"

        else:

            cfg_path = serv.fileutil.path / serv.fileutil.config_default

            if cfg_path.is_file():

                with open(cfg_path, "rb") as f:

                    cfg_sha = sha256(f.read()).hexdigest()

                local_sha_line = f"  > SHA256 (config):  [{cfg_sha}]"

            else:

                local_sha_line = "  > SHA256:  [Unavailable]"

        output("\n+=============================================================================+")
        output("# Local Server Version Information:")
        output(f"  > Version: [{local_version}]")
        output(f"  > Build:   [{local_build}]")
        output(local_sha_line)
        output("+=============================================================================+\n")

        builds_for_status = serv.update.get_buildnums(local_version)

        latest_build = max(builds_for_status) if builds_for_status else selected_build

        meta = serv.update.build_download_url(local_version, latest_build)

        remote_sha = (meta.get('checksums', {}) or {}).get('sha256', '').lower()

        output("+=============================================================================+")
        output("# Remote Server Version Information:")
        output(f"  > Version: [{local_version}]")
        output(f"  > Build:   [{latest_build}]")

        if remote_sha:

            output(f"  > SHA256:  [{remote_sha}]")

        else:

            output("  > SHA256:  [Unavailable]")

        output("+=============================================================================+\n")

        sys.exit(EXIT_NOTHING)

    except Exception as e:

        error_report(e, net=isinstance(e, URLError))

        sys.exit(EXIT_NOTHING)

if args.stats:

    serv.view_data()

    sys.exit(EXIT_NOTHING)

if args.script_version:

    output(f"\n\n+===============================================================+\n")
    output(f"   PaperMC Updater Script - version: {__version__}\n")
    output(f"   Contact GitHub: {GITHUB}")
    output(f"   Current Python Version: {sys.version_info.major}.{sys.version_info.minor}.{sys.version_info.micro} ({platform.system()})")
    output(f"\n+===============================================================+\n")

    sys.exit(EXIT_NOTHING)

serv.start()

name = None

if args.output:

    name = args.output

elif args.path.is_file():

    name = args.path.name

if not args.no_check and not args.new and not args.interactive:

    update_available = serv.check(args.version, args.build)

else:

    if args.no_check:

        output("\n# Skipping Version Check (forced: --no-check)")

if not args.check_only and update_available:

    if args.no_backup:

        output("# Skipping Backup (forced: --no-backup)")

    elif args.new:

        output("\n# Skipping Backup (new install)")

    res = serv.get_new(default_version=args.version, default_build=args.build,
                       backup=not (args.no_backup or args.new),
                       new=args.new, output_name=name, target_copy=args.copy_old)

    if res:

        sys.exit(EXIT_UPDATE)  # success: update installed

    else:

        sys.exit(EXIT_NOTHING)
