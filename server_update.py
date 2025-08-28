#!/usr/bin/env python3
# (Shebang for Linux/macOS; ignored on Windows as # comment)

from __future__ import annotations

import sys

# Before we do ANYTHING, we check to make sure python is the correct version!

if sys.version_info < (3,7,0):

    sys.stdout.write("\n--== [ Invalid python version! ] ==--\n")
    sys.stdout.write("Current version: {}\n".format(sys.version_info))
    sys.stdout.write("Expected version: 3.7+\n")
    sys.stdout.write("\nPlease install the correct version of python before continuing!\n")

    sys.exit(10)

import tempfile
import urllib.request
import shutil
import json
import traceback
import argparse
import os
import subprocess
import platform
import time
import socket

from urllib.error import URLError
from http.client import HTTPResponse
from hashlib import sha256
from typing import Any, Callable, List, Sequence, Tuple, Union
from json.decoder import JSONDecodeError
from math import ceil
from pathlib import Path
from textwrap import dedent


"""
A Set of tools to automate the server update process.
"""

__version__ = '4.1.1c'

# These variables contain links for the script updating process.

GITHUB = 'https://github.com/Creeper36/PaperMC-Update'
GITHUB_RELEASE = 'https://api.github.com/repos/Creeper36/PaperMC-Update/releases/latest'
GITHUB_RAW = 'https://raw.githubusercontent.com/Creeper36/PaperMC-Update/master/server_update.py'


filterArray = [
    "[PaperMC", "[Handles", "[Written", "[ --== Moving", "[ --== Paper", "# Loading build", "# Removed",
    "[ --== Checking", "|  ", "[ --== Version", "[ --== Starting", "[ --== End", "# Done",
    "# Selecting latest", "*****", "+====", "# Temporary", "# Saved", "# Loading version"
]


quietmode = any(flag in sys.argv for flag in ("-q", "--quiet"))

if quietmode:

    import builtins

    builtins.print = lambda *a, **k: None

    try:

        sys.stdout.write = lambda *a, **k: None

        sys.stderr.write = lambda *a, **k: None

    except Exception:

        pass


def _is_windows():

    return platform.system().lower() == "windows"


def check_internet_connection():
    """
    Attempts up to 4 pings to 8.8.8.8.
    If any ping succeeds, the function continues on the script.
    If all 4 fail, prints an error and exits with status code 2.
    On Linux/Unix: 'ping' command may be missing. if ping fails, it will attempt
    a fallback socket test. if still fails, will error message and exit.
    """

    for attempt in range(4):

        try:

            if _is_windows():

                cmd = ["ping", "-n", "1", "8.8.8.8"]

            else:

                cmd = ["ping", "-c", "1", "8.8.8.8"]

            rc = subprocess.run(cmd, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL).returncode

            if rc == 0:

                return  # success

        except FileNotFoundError:

            # Fallback: socket test if ping command not found

            try:

                with socket.create_connection(("8.8.8.8", 53), timeout=3):

                    return

            except OSError:

                pass

        time.sleep(1)

    if _is_windows():

        print("# ERROR: No Internet Connection detected!")
       
    else:

        print("# ERROR: No Internet Connection detected (Linux/Unix: 'ping' may be missing. Please install 'iputils-ping' or similar.)")

    sys.exit(3)


def load_local_version(serv: ServerUpdater) -> tuple[str, int]:
    """
    Loads local version/build from version_history.json via FileUtil.
    Returns (version, build).
    """

    try:

        version, build = serv.fileutil.load_config(serv.config_file)

        return version, build

    except Exception as e:

        output(f"# ERROR loading local version info: {e}")

        return ("unknown", -1)


def load_config_old(config: dict) -> Tuple[str, int]:
    """
    Loads configuration data from the given file.

    We only load version info if it's in the official format!
    We return the version and build number found in the configuration file.

    This function looks for config data in the old format,
    which at this time seems to be pre 1.21 (TODO: Confirm)
    We preform a check to see if the data looks correct,
    the current version string MUST start with 'git-Paper',
    otherwise we will raise a value error. 

    :param config: JSON data to consider
    :type config: dict
    :return: Tuple containing version and build data respectively
    :rtype: Tuple[str, int]
    """

    OLD_PREFIX = 'git-Paper'  # Old prefix

    # Read the data, and attempt to pull some info out of it

    current = config['currentVersion']

    # Ensure string prefix is correct:

    if not OLD_PREFIX == current[:len(OLD_PREFIX)]:

        # Does not match! Must be invalid ...

        raise ValueError("Invalid old config data format!")

    # Splitting the data in two so we can pull some content out:

    build, version = current.split(" ", 1)

    # Getting build information:

    build = int(build.split("-")[-1])

    # Getting version information:

    version = version[5:-1]

    # Returning version information:

    return version, build


def load_config_new(config: dict) -> Tuple[str, int]:
    """
    Loads configuration data from the given file.

    We only load version info if it's in the official format!
    We return the version and build number found in the configuration file.

    This function looks for config data in the new format,
    which at this time seems to be post 1.21 (TODO: Confirm)

    :param config: JSON data to consider
    :type config: dict
    :return: Tuple containing version and build data respectively
    :rtype: Tuple[str, int]
    """

    # Read the data, and attempt to pull some info out of it

    current = config['currentVersion']

    # Splitting the data in two so we can pull some content out:

    split = current.split(" ")[0].split("-")

    # Getting build information:

    build = int(split[1])

    # Getting version information:

    version = split[0]

    # Returning version information:

    return version, build


def upgrade_script(serv: ServerUpdater, force: bool = False):
    """
    Upgrades this script.
    
    We do this by checking github for any new releases,
    comparing them to our version,
    and then updating if necessary.
    
    We use the ServerUpdater to do this operation for us,
    so you will need to provide it for this function
    to work correctly.

    :param serv: ServerUpdater to use
    :type serv: ServerUpdater
    """

    if not args.batch:

        output("\n[ --== Starting Script Upgrade: ==-- ]\n")
    
    # Creating request here:

    req = urllib.request.Request(GITHUB_RELEASE, headers={'Accept': 'application/vnd.github.v3+json'})

    # Getting data:

    try:

        resp = urllib.request.urlopen(req)

        data = json.loads(resp.read())

    except URLError as e:

        # Network / DNS / timeout / refused, etc.

        error_report(e, net=True)

        return

    except JSONDecodeError as e:

        # Got a response but it wasn't valid JSON

        error_report(e)

        return

    except Exception as e:

        # Any other unexpected problem

        error_report(e)

        return

    if not force and data.get('tag_name') == __version__:

        output("# No upgrade necessary!\n")

        return

    if force and data.get('tag_name') == __version__:

        output("# Force script download")
    else:
        output("# New version available!")

    url = GITHUB_RAW

    path = Path(__file__).resolve().absolute()

    # Determine if we are working in a frozen environment:
    
    if getattr(sys, 'frozen', False):
        
        print("# Can't upgrade frozen files!")

        return

    serv.fileutil.path = path

    # Getting data:

    if not args.batch:

        output("\n[ --== Starting Download: ==-- ]\n")

    if args.batch:

        output ("# Starting download...")

    serv.fileutil.create_temp_dir()

    temp_path = Path(serv.fileutil.temp.name).expanduser().resolve() / 'temp'

    req = urllib.request.Request(url)

    with urllib.request.urlopen(req) as resp:

        total = int(resp.info().get("Content-Length", 0))

        chunk = 8192

        use_progress = (not args.batch and not args.quiet and total > 0)

        if use_progress:

            steps = max(1, (total + chunk - 1) // chunk)

        with open(temp_path, "wb") as f:

            step_idx = 0

            while True:

                buf = resp.read(chunk)

                if not buf:

                    if use_progress:

                        progress_bar(total, chunk, steps, steps - 1)

                    break

                f.write(buf)

                if use_progress:

                    # call progress_bar once per chunk

                    progress_bar(total, chunk, steps, min(step_idx, steps - 1))

                    step_idx += 1

    if not args.batch:

        output("\n[ --== Download Complete! ==-- ]")

    if args.batch:

        output("# Download complete!")

    # Move the new script:

    serv.fileutil.install(temp_path, path)

    # We are done!

    if not args.batch:

        output("\n[ --== Script Upgrade Complete! ==-- ]")

    else:

        output("# Script upgrade complete!")

    sys.exit(2)


def output(text: str, args=None):
    """
    Outputs text to the terminal via print.
    Will not print content if we are in quiet mode,
    and will apply batch-mode filters if in batch mode.
    """

    if args.quiet:

        return

    if args.batch:

        if not text.strip():

            return

        for pattern in filterArray:

            if pattern in text:

                return

    print(text.strip() if args.batch else text)


def error_report(exc, net: bool=False):
    """
    Function for displaying error information to the terminal.

    :param exc: Exception object
    :param net: Whether to include network information
    :type net: bool
    """

    print("+==================================================+")
    print("  [ --== The Following Error Has Occurred: ==-- ]")
    print("+==================================================+")

    # Print error name

    print("Error Name: {}".format(exc))
    print("+==================================================+")

    # Print full traceback:

    print("Full Traceback:")
    traceback.print_exc()

    if net:

        # Include extra network information

        print("+==================================================+")
        print("Extra Network Information:")


        if hasattr(exc, 'url'):

            print("Attempted URL: {}".format(exc.url))

        if hasattr(exc, 'reason'):

            print("We failed to reach the server.")
            print("Reason: {}".format(exc.reason))

        if hasattr(exc, 'code'):

            print("The server could not fulfill the request.")
            print("Error code: {}".format(exc.code))

    print("+==================================================+")
    print("(Can you make anything of this?)")
    print("Please check the github page for more info: https://github.com/Creeper36/PaperMC-Update.")

    return


def progress_bar(length: int, stepsize: int, total_steps: int, step: int, prefix: str="Downloading:", size: int=60, prog_char: str="#", empty_char: str="."):
    """
    Outputs a simple progress bar to stdout.

    We act as a generator, continuing to iterate and add to the bar progress
    as we download more information.

    :param length: Length of data to download
    :type length: int
    :param stepsize: Size of each step
    :type stepsize: int
    :param total_steps: Total number of steps
    :type total_steps: int
    :param step: Step number we are on
    :type step: int
    :param prefix: Prefix to use for the progress bar
    :type prefix: str
    :param size: Number of characters on the progress bar
    :type size: int
    :param prog_char: Character to use for progress
    :type prog_char: str
    :param empty_char: Character to use for empty progress
    :type empty_char: str
    """

    # Calculate number of '#' to render:

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
    Server updater, handles checking, downloading, and moving.

    This class facilitates communication between this script and the Paper v2 API.
    We offer methods to retrieve available versions, builds, 
    and other information about downloads.
    Users can download the final jar file using this class as well.
    We also offer the ability to generate download URLs,
    so the user can download the files in any way they see fit. 
    """

    def __init__(self, user_agent: str = ''):

        self._base = 'https://fill.papermc.io/v3/projects/paper'  # Base URL to build of off

        self._headers = {
             'Content-Type': 'application/json;charset=UTF-8',
             'Accept': 'application/json, text/plain, */*',
             'User-Agent': f'PaperMC-Update/{__version__} (https://github.com/Creeper36/PaperMC-Update)',
             'Accept-Language': 'en-US,en;q=0.5',
             'DNT': '1',
         }

        # Determine if we need to change the user agent in the headers

        if user_agent:

          # We must change the user agent to the provided value

          self._headers['User-Agent'] = user_agent

        self.download_path = ''  # Path the file was downloaded to

        self.cache = {}  # A basic cache for saving responses

    def _none_function(self, length, blocksize, total, step, *args, **kwargs):
        """
        Dummy function that does nothing.
        """

        pass

    def version_convert(self, ver: str) -> Tuple[int,int,int]:
        """
        Converts the version string into a tuple that can be used for comparison.

        This tuple contains three numbers, each of which can be used
        in equality operations.
        This can be used to determine if a given version is greater or lessor than another.

        :param ver: Version string to convert
        :type ver: str
        :return: Tuple contaning version information
        :rtype: Tuple[int,int,int]
        """

        # Convert and return the tuple:

        temp: List[int] = []

        for item in ver.split('.'):

            # Convert and add the item:

            temp.append(int(item))

        return (temp[0], temp[1], temp[2])

    def build_data_url(self, version: str=None, build_num: int=None) -> str:
        """
        Builds a valid URL for retrieving version data.

        The user can use this URL to retrieve various versioning data.

        If version and build_num are not specified,
        then general paper info is returned:

        https://papermc.io/api/v2/projects/paper

        If build_num is not specified, 
        then general data about the specified data is returned:

        https://papermc.io/api/v2/projects/paper/versions/[version]

        If both arguments are provided,
        then data about the specific version and build is returned:

        https://papermc.io/api/v2/projects/paper/versions/[version]/builds/[build_num]

        :param version: Version to fetch info for, defaults to None
        :type version: str, optional
        :param build_num: Build number to get info for, defaults to None
        :type build_num: int, optional
        :return: URL of the data
        :rtype: str
        """

        # Building url:

        final = self._base

        if version is not None:

            # Specific version requested:

            final = final + '/versions/' + str(version)

            if build_num is not None:

                # Specific build num requested:

                final = final + '/builds/' + str(build_num)

        # Return the URL:

        return final

    def build_download_url(self, version: str, build_num:int) -> dict[str, dict[str, Union[str, int, dict[str, str]]]]:
        """
        Builds a valid download URL that can be used to download a file.
        We use the version and build number to generate this URL.

        The user can use this URL to download the file
        using any method of their choice.
        In addition to the download URL,
        we also provide the filesize, SHA256 checksum, and default filename.

        :param version: Version to download
        :type version: str
        :param build_num: Build number to download, defaults to 'latest'
        :type build_num: str, optional
        """

        ##
        # New in V3
        ##

        # The API now directly gives us a download URL,
        # Along with the size, checksum, and default filesname.
        # We now return the download URL, along with these newly provided values.

        # Make the call, extract the relevant data, and return

        return self.get(version, build_num)['downloads']['server:default']

    def download_response(self, url: str) -> HTTPResponse:
        """
        Calls the underlying urllib library and return the object generated.

        This object is usually a HTTPResponse object.
        The user can use this object in any way they see fit.
        Users MUST provide a URL to a file to download!
        
        :param url: URL of file to download
        :type url: str
        :return: Object returned by urllib
        :rtype: HTTPResponse
        """

        # Creating request here:

        req = urllib.request.Request(url, headers=self._headers)

        # Sending request to Paper API

        return urllib.request.urlopen(req)

    def download_file(self, path: Path, version: str, build_num:int, check:bool=True, call: Callable=None, args: List=None, blocksize: int=4608) -> Path:
        """
        Downloads the content to the given external file.
        We handle all file operations,
        and automatically work with the URLResponse objects
        to write the file contents to an external file.

        If a directory is provided, 
        then we will use the recommended name of the file,
        and save it to the directory provided.

        Users can also pass a function to be called upon each block of the download.
        This can be useful to visualize or track downloads.
        We will pass the total length, stepsize, total steps, and step number.
        The args provided in the args parameters will be passed to the function as well.

        :param path: Path to directory to write to
        :type path: str
        :param version: Version to download
        :type version: str
        :param build_num: Build to download
        :type build_num: int
        :param check: Boolean determining if we should check the integrity of the file
        :type check: bool
        :param call: Method to call upon each download iteration
        :type call: Callable
        :param args: Args to pass to the callable
        :type args: List
        :param blocksize: Number of bytes to read per copy operation
        :type blocksize: int
        :return: Path the file was saved to
        :raises: ValueError: If file integrity check fails
        """

        if args is None:

            args = []

        if call is None:

            call = self._none_function

            args = []

        # First, get the file data

        ddata = self.build_download_url(version, build_num)

        # Get the data:

        data = self.download_response(str(ddata['url']))

        # Get filename for download:

        if path.is_dir():

            # Use the default name:

            path = path / str(ddata['name'])

        # Get length of file:

        length: int = int(ddata['size'])

        total = ceil(length/blocksize) + 1

        # Open the file, we want to read it as well for verification,
        # so we specify the + symbol to open for reading and writing

        file = open(path, mode='bw+')

        # Copy the downloaded data to the file:

        for i in range(total):

            # Call the method:

            call(length, blocksize, total, i, *args)

            # Get the data:

            file.write(data.read(blocksize))

        # Ensure the right checksum is available
        # (According to the schema, they only provide sha256 sums, but better be safe than sorry)

        if check and 'sha256' in ddata['checksums'].keys():

            # Get the ideal SHA256 hash for the file:

            hash = ddata['checksums']['sha256']

            # We gotta seek to the beginning of the file,
            # since our pointer is now at the end

            file.seek(0)

            # Now checking integrity, again we only expect to work with SHA256

            if not sha256(file.read()).hexdigest() == hash:

                # File integrity failed! Do something...

                raise ValueError("File integrity check failed!")

        # Closing file:

        file.close()

        return path

    def get_versions(self) -> list[str]:
        """
        Gets available versions of the server.

        The list of versions is a tuple of strings.
        Each version follows the Minecraft game version conventions.

        :return: List of available versions
        """

        # Get the version map

        vmap: dict[str, list[str]] = self.get()['versions']

        ##
        # New in V3
        ##

        # The API now provides us with a dictionary mapping major versions with sub-versions.
        # Previously, it was like this: ['1.14.4', '1.14.3', '1.14.2', '1.14.1', '1.14', '1.13.2', ...]
        # Now, it is like this: {'1.14': ['1.14.4', '1.14.3', '1.14.2', '1.14.1', '1.14'], '1.13': [...], ...}
        # In addition, the order of releases are reversed, it used to be oldest -> newest, but now it's newest -> oldest
        # So, for compatibility reasons, we need to squish this mapping of arrays in a single array, and then reverse sort it

        # Define final array to contain results

        versions: list[str] = []

        # Iterate over each key and value in the mapping

        for _, value in vmap.items():

            # Iterate over each version in the values

            for val in value:

                # Add the value to the master list

                versions.append(val)

        # Versions in dictionary are in order
        # (Dictionary keys are in the order they are added since python 3.7, the minimum python version),
        # but we need to reverse

        versions.reverse()

        # Finally, return the version info

        return versions

    def get_buildnums(self, version: str) -> list[int]:
        """
        Gets available build for a particular version.

        The builds are a tuple of ints,
        which follow PaperMC build number conventions.

        :param version: Version to get builds for
        :type version: str
        :return: List of builds
        :rtype: Tuple[int,...]
        """

        ##
        # New in V3
        ##

        # The build numbers are now reversed, going from newest to oldest.
        # This script expects the build numbers to be from oldest to newest,
        # So we will reverse this list

        # Get the list from the API

        builds: list[int] = self.get(version)['builds']

        # Reverse the list

        builds.reverse()

        # Return the build info

        return builds

    def get(self, version: str=None, build_num: int=None) -> dict:
        """
        Gets RAW data from the Paper API, version info only.

        We utilize some basic caching to remember responses
        instead of calling the PaperMC API multiple times. 

        You can use this to get a list of valid versions,
        list of valid builds per version,
        as well as general data related to the selected version.

        You should check out:

        https://paper.readthedocs.io/en/latest/site/api.html
        https://papermc.io/api/docs/swagger-ui/index.html?configUrl=/api/openapi/swagger-config#/

        For more information on PaperMC API formatting.

        We return the data in a dictionary format.

        :param version: Version to include in the URL
        :type version: str
        :param build_num: Build number to include in the URL
        :type build_num: int
        :return: Dictionary of request data
        :rtype: dict
        """

        # Generate URL:

        url = self.build_data_url(version, build_num)

        # Check if we have saved content:

        if url in self.cache.keys():

            # We have cached content:

            return self.cache[url]

        # Get the data and return:

        data = json.loads(self._get(version, build_num).read())

        # Cache it:

        self.cache[url] = data

        # Return the final data:

        return data

    def _get(self, version: str=None, build_num: int=None) -> HTTPResponse:
        """
        Gets raw data from the PaperMC download API.

        This method generates the relevant URLs and returns
        the HTTPResponse object representing the request.

        :param version: Version to get info for, defaults to None
        :type version: str, optional
        :param build_num: Build to get info for, defaults to None
        :type build_num: int, optional
        :return: HTTPResponse representing the request
        :rtype: HTTPResponse
        """

        final = self.build_data_url(version, build_num)

        # Check if the URL is present in the cache:

        if final in self.cache.keys():

            # Cached content is found, return THAT:

            return self.cache[final]

        # Creating request here:

        req = urllib.request.Request(final, headers=self._headers)

        # Getting data:

        data = urllib.request.urlopen(req)

        # Saving data:

        self.cache[final] = data

        return data


class FileUtil:
    """
    Class for managing the creating/deleting/moving of server files.
    """

    def __init__(self, path, interactive=False):

        self.path: Path = Path(path).expanduser().resolve().absolute()

        self.temp: tempfile.TemporaryDirectory

        self.config_default = 'version_history.json'

        self.target_path = ''

        self.interactive = interactive

    def create_temp_dir(self):
        """
        Creates a temporary directory.

        :return: Temp file instance
        """

        self.temp = tempfile.TemporaryDirectory()

        return self.temp

    def close_temp_dir(self):
        """
        Closes created temporary directory.
        """

        self.temp.cleanup()

    def load_config(self, config: str) -> Tuple[str, int]:
        """
        Loads configuration info from 'version_history.json' in the server directory
        We only load version info if it's in the official format!

        :param config: Path to config file
        :type config: str
        :return: (version, build)
        """

        if config is None:

            # Need to determine our config path:

            if self.path.is_dir():

                config = self.path / self.config_default

            else:

                config = self.path.parent / self.config_default

        output("# Loading data from file [{}] ...".format(config))

        if not Path(config).is_file():

            # Walk upwards until root

            current = Path(config).parent

            found = None

            while current != current.parent:  # stop at filesystem root

                candidate = current / Path(config).name

                if candidate.is_file():

                    found = candidate

                    break

                current = current.parent

            if found:

                output("# Falling back to [{}] ...".format(found))

                config = found

            else:

                if _is_windows():

                    fallback = Path(r"C:\minecraft") / "version_history.json"

                    if fallback.is_file():

                        output("# Falling back to [{}] ...".format(fallback))

                        config = fallback

                    else:

                        print("# Unable to load config data from file [{}] - Not found in any parent directories!".format(config))

                        return '0', 0

                else:

                    print("# Unable to load config data from file [{}] - Not found in any parent directories!".format(config))

                    return '0', 0

        # Load file content

        try:

            # Open file

            with open(config, 'r') as file:

                # Decode file

                data = json.load(file)

        except JSONDecodeError:

            # Data not in valid JSON format.

            output("# Failed to load config data - Not in JSON format!")

            return '0', 0

        try:

            # First, try old format...

            return load_config_old(data)

        except Exception:

            # Did not work, try something else ...

            pass

        # Try new format:

        try:

            return load_config_new(data)

        except Exception:

            # Extra weird errors due to formatting issues:

            output("# Failed to load config data - Strange format, we support official builds only!")

            return '0', 0

    def install(self, file_path: str, new_path: str, target_copy: str=None, backup=True, new=False):
        """
        "Moves" the contents of the temporary file into the target in the root server directory.

        The new file should exist in the temporary directory before this method is invoked!

        We backup the old jar file by default to the temporary directory,
        and we will attempt to recover the old jar file in the event of any failures.
        This feature can be disabled.

        :param file_path: The path to the new file to move
        :type new_file: str
        :param new_path: Path to move the file to
        :type new_path: str
        :param target_copy: Where to copy the old file to
        :type target_copy: str
        :param file_name: What to rename the new file to, None for no change
        :type file_name: str
        :param backup: Value determining if we should back up the old file
        :type backup: bool
        :param new: Determines if we are doing a new download, aka if we care about file operation errors
        :type new: bool
        """

        if not args.upgrade:

            output("\n[ --== Moving Files To Target: ==-- ]\n")

        if self.interactive:

            output(f"# Interactive mode: moving as '{self.path.name}'")

        else:

            # === AUTOMATED MODE: Validate, back up, and move/replace

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

                try:

                    shutil.copyfile(self.path, Path(self.temp.name) / 'backup')

                except Exception as e:

                    self._fail_install("File Backup")

                    error_report(e)

                self.target_path = new_path

                output(f"# Backup created at: {Path(self.temp.name) / 'backup'}")

            try:

                final_path = self.path.parent / new_path


                if _is_windows():

                    # ---- Windows path (keep old behavior) ----

                    if self.path.is_file():

                        output("# Deleting existing file at {} ...".format(self.path))

                        try:

                            os.remove(self.path)

                        except PermissionError as e:

                            if getattr(e, "winerror", None) == 32:

                                output(f"\n# [ERROR] Cannot delete '{self.path.name}', it is currently locked / IN-USE.")

                                output("# Please close the Minecraft server (or any process using this file) and try again.")

                                sys.exit(10)

                            else:

                                raise

                        except Exception as e:

                            self._fail_install("Old File Deletion")
                            error_report(e)

                            sys.exit(10)

                        output("# Removed original file!")

                    # Copy new file into place

                    output("# Moving download data to target location ...")

                    output(f"# ({file_path} > {final_path})")

                    shutil.copyfile(file_path, final_path)

                else:

                    # ---- POSIX (Linux/Unix/macOS): atomic replace ----

                    output("# Moving download data to target location (staged replace) ...")

                    staging = final_path.with_suffix(final_path.suffix + ".updating")

                    shutil.copyfile(file_path, staging)

                    os.replace(staging, final_path)

            except Exception as e:

                self._fail_install("File Move")

                error_report(e)

                if not self.interactive and backup and self.path.is_file() and not new:

                    self._recover_backup()

                return False

        output("# Done moving download data to target location!")

        if not args.upgrade:

            output("\n[ --== Moving Files Complete! ==-- ]")

        return True


    def _recover_backup(self):
        """
        Attempts to recover the backup of the old server jar file.
        """

        print("+==================================================+")
        print("\n> !ATTENTION! <")
        print("A failure has occurred during the downloading process.")
        print("I'm sure you can see the error information above.")
        print("This script will attempt to recover your old file.")
        print("If this operation fails, check the github page for more info: "
              "https://github.com/Creeper36/PaperMC-Update")

        # Deleting file in root directory:

        print("# Deleting Corrupted temporary File...")

        try:

            os.remove(self.target_path)

        except FileNotFoundError:

            # File was not found. Continuing...

            print("# File not found. Continuing operation...")

        except Exception as e:

            print("# Critical error during recovery process!")
            print("# Displaying error information:")

            error_report(e)

            print("Your previous file could not be recovered.")

            return False

        # Copying file to root directory:

        print("# Copying backup file[{}] to server root directory[{}]...".format(Path(self.temp.name) / 'backup'),
                                                                                 self.path)

        try:

            shutil.copyfile(Path(self.temp.name) / 'backup', self.path)

        except Exception as e:

            print("# Critical error during recovery process!")
            print("# Displaying error information:")

            error_report(e)

            print("Your previous file could not be recovered.")

            return False

        print("\nRecovery process complete!")
        print("Your file has been successfully recovered.")
        print("Please debug the situation, and figure out why the problem occurred,")
        print("Before re-trying the update process.")

        return True

    def _fail_install(self, point):
        """
        Shows where the error occurred during the download.

        :param point: Point of failure
        """

        print("\n+==================================================+")
        print("> !ATTENTION! <")
        print("An error occurred during the download, and we can not continue.")
        print("We will attempt to recover your previous file (If applicable)")
        print("Fail point: {}".format(point))
        print("Detailed error info below:")

        return


class ServerUpdater:
    """
    Class that binds all server updater classes together
    """

    def __init__(self, path, config_file: str='', version='0', build=-1, config=True, prompt=True, integrity=True, user_agent: str = ''):

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
        Starts the object, loads configuration.
        """

        temp_version = '0'

        temp_build = 0

        if self.config:

            temp_version, temp_build = self.fileutil.load_config(self.config_file)

        if self.version != '0' or self.buildnum != 0:

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
        Outputs the current server version and build to the terminal.
        """
        v = self.version if version is None else version

        b = self.buildnum if build is None else build

        output("\n# Server Version Information:")

        output("  > Version: [{}]".format(v))

        output("  > Build: [{}]".format(b))


    def view_data(self):
        """
        Displays data on the selected version and build.

        We display the version, build, time,
        commit changes, filename, and the sha256 hash.

        Unlike version_select(), this bypasses interactive
        prompts and the 'Version Selection' banner so that
        --stats runs cleanly and only prints stats.
        """

        try:

            versions = self.update.get_versions()

        except Exception as e:

            self._url_report("API Fetch Operation")

            error_report(e, net=isinstance(e, URLError))

            return

        ver = self._select(args.version, versions, 'latest', 'version', print_output=False)

        if not ver:

            return

        try:

            builds = list(self.update.get_buildnums(ver))

        except Exception as e:

            self._url_report("API Fetch Operation")

            error_report(e, net=isinstance(e, URLError))

            return

        if not builds:

            print("# No builds available for version", ver)

            return

        build = self._select(args.build, builds, -1, 'buildnum', print_output=False)

        if not build:

            return

        # Get the data

        data = self.update.get(ver, build)

        output("\n+==================================================+")
        output("\n[ --== Paper Stats: ==-- ]\n")
        output(f"Version: {ver}")
        output(f"Build Number: {build}")
        output(f"Creation Time: {data['time']}")
        output(f"File name: {data['downloads']['server:default']['name']}")
        output(f"SHA256 Hash: {data['downloads']['server:default']['checksums']['sha256']}")

        for num, change in enumerate(data['commits']):
            output("\nChange {}:\n".format(num))
            output("Commit ID: {}".format(change['sha']))
            output("Commit Time: {}".format(change['time']))
            output("Commit Message: {}".format(change['message']))

        output("\n[ --== End Paper Stats! ==-- ]\n")
        output("+==================================================+\n")

    def check(self, default_version: str, default_build: int):
        """
        Checks if a new version is available.

        :param default_version: Default version to move
        :type default_version: str
        :param default_build: Default build to move
        :type default_build: int
        :return: True is new version, False if not/error
        """

        output("\n[ --== Checking For New Version: ==-- ]\n")

        # Checking for new server version

        output("# Loading version information ...")

        try:

            ver = self.update.get_versions()

        except URLError as e:

            self._url_report("API Fetch Operation")

            # Report the error

            error_report(e, net=True)

            return False

        except Exception as e:

            self._url_report("API Fetch Operation")

            # Report the error

            error_report(e)

            return False

        output("# Comparing local <> remote versions ...")

        if self.version != self._select(default_version, ver, 'latest', 'version', print_output=False) and (self.version == '0' or ver[-1] != self.version):

            # New version available!

            output("# New Version available! - [Version: {}]".format(ver[-1]))
            output("\n[ --== Version check complete! ==-- ]")

            return True

        output("# No new version available.")

        # Checking builds

        output("# Loading build information ...")

        try:

            build = self.update.get_buildnums(self.version)

        except URLError as e:

            self._url_report("File Download")

            # Report the error

            error_report(e, net=True)

            return False

        except Exception as e:

            self._url_report("File Download")

            # Report the error

            error_report(e)

            return False

        output("# Comparing local <> remote builds ...")

        if self.buildnum != self._select(default_build, build, 'latest', 'buildnum', print_output=False) and (self.buildnum == 0 or build[-1] != self.buildnum):

            # New build available!

            output("# New build available! - [Build: {}]".format(build[-1]))
            output("\n[ --== Version check complete! ==-- ]")

            return True

        output("# No new build available.")
        output("\n[ --== Version check complete! ==-- ]")

        return False

    def version_select(self, default_version: str='latest', default_build: int=-1) -> Tuple[str, int]:
        """
        Prompts the user to select a version to download,
        and checks input against values from Paper API.
        Default value is recommended option, usually 'latest'.

        :param default_version: Default version
        :type default_version: str
        :param default_build: Default build number
        :type default_build: int
        :return: (version, build)
        """

        if self.version_install is not None and self.build_install is not None:

            # Already have a version and build selected, return:

            return self.version_install, self.build_install

        output("\n[ --== Version Selection: ==-- ]")

        new_default = str(default_build)

        if new_default == '-1':

            # Convert into something more readable:

            new_default: str = 'latest'

        # Checking if we have version information:

        if not self.prompt:

            output("# Loading version information ...")
        
        try:

            versions = self.update.get_versions()

        except URLError as e:

            self._url_report("API Fetch Operation")

            # Report the error

            error_report(e, net=True)

            return '', -1

        except Exception as e:

            self._url_report("API Fetch Operation")

            # Report the error

            error_report(e)

            return '', -1

        if self.prompt:

            print("\nPlease enter the version you would like to download:")
            print("Example: 1.4.4")
            print("(Tip: <DEFAULT> Option Is Enclosed In Angle Brackets <>. Press <ENTER> to accept it.)")
            print("(Tip: Enter 'latest' to select the most recent version of paper.)")

            print("\nAvailable versions:")

            # Displaying available versions

            for i in versions:

                print("  Version: [{}]".format(i))

            while True:

                ver = input("\nEnter Version <{}>: ".format(default_version))

                ver = self._select(ver, versions, default_version, "version")

                if ver:

                    break

        else:

            # Just select default version

            ver = self._select('', versions, default_version, "version")

            if not ver:

                # Invalid version selected

                print("# Aborting download!")

                return '', -1

        # Getting build info

        output("# Loading build information ...")

        try:

            nums = list(self.update.get_buildnums(ver))

        except URLError as e:

            self._url_report("API Fetch Operation")

            # Report the error

            error_report(e, net=True)

            return '', -1

        except Exception as e:

            self._url_report("API Fetch Operation")

            # Report the error

            error_report(e)

            return '', -1

        # Check if their are no builds:
        
        if len(nums) == 0:
            
            # No builds available, abort:

            print("# No builds available!")
            print("\nThe version you have selected has no builds available.")
            print("This could be because the version you are attempting to download is too new or old.")
            print("The best solution is to either wait for a build to be produced for your version,")
            print("Or select a different version instead.")

            print("\nTo see if a specific version has builds, you can issue the following command:\n")
            print("python server_update.py -nc --version [version]")
            print("\nSimply replace [version] with the version you wish to check.")
            print("This message will appear again if there are still no builds available.")
            print("The script will now exit.")

            return '', -1

        if self.prompt:

            print("\nPlease enter the build you would like to download:")
            print("Example: 205")
            print("(Tip: <DEFAULT> Option Is Enclosed In Angle Brackets <>. Press <ENTER> to accept it.)")
            print("(Tip: Enter 'latest' to select the most recent build of paper.)")

            print("\nAvailable Builds:")

            # Displaying available builds

            new = []

            for i in sorted(nums, key=int):

                print("  > Build Num: [{}]".format(i))
                new.append(str(i))

            while True:

                # Prompting user for build info

                build = input("\nEnter Build <{}>: ".format(new_default))

                print(new_default)

                build = self._select(build, new, new_default, "build")

                if build:

                    # User selected okay value
 
                    break

        else:

            # Select default build

            build = self._select('', nums, new_default, "build")

            if not build:

                # Invalid build selected!

                output("# Aborting download!")

                return '', -1

        output("\n# Selection made:")
        output("   > Version: [{}]".format(ver))
        output("   > Build: [{}]".format(build))

        output("\n[ --== Version Selection Complete! ==-- ]")

        # Setting our values:

        self.version_install = str(ver)

        self.build_install = int(build)

        return self.version_install, self.build_install

    def get_new(self, default_version: str='latest', default_build: int=-1, backup: bool=True, new: bool=False, 
            target_copy: str=None, output_name: str=None):
        """
        Downloads the new version,
        Prompts the user to select a specific version.

        After the version is selected,
        then we invoke the process of downloading the the file,
        and moving it to the current location.

        :param default_version: Default version to select if none is specified
        :type default_version: str
        :param default_build: Default build to select if none is specified
        :type default_build: str
        :param backup: Value determining if we should back up the old jar file
        :type backup: bool
        :param new: Value determining if we are doing a new download
        :type new: bool
        :param target_copy: Path we should copy the old file to
        :type no_delete: str
        :param output_name: Name of the new file. None to keep original name
        :type output_name: str
        """

        # Prompting user for version info:

        ver, build = self.version_select(default_version=default_version, default_build=default_build)

        if ver == '' or build == -1:

            # Error occurred, cancel download

            return

        # Checking if user wants to continue with download

        if self.prompt:

            print("\nDo you want to continue with the download?")

            inp = input("(Y/N):").lower()

            if inp in ['n', 'no']:
                # User does not want to continue, exit

                output("Canceling download...")

                return

        # Creating temporary directory to store assets:

        output("\n# Creating temporary directory...")

        self.fileutil.create_temp_dir()

        output("# Temporary directory created at: {}".format(self.fileutil.temp.name))

        # Starting download process:

        if not args.batch:

            output("\n[ --== Starting Download: ==-- ]\n")

        if args.batch:

            output("# Starting download...")

        try:

            path = self.update.download_file(Path(self.fileutil.temp.name), ver, build_num=build, call=progress_bar, check=self.integrity)

        except URLError as e:

            self._url_report("File Download")

            # Report the error

            error_report(e, net=True)

            return False

        except ValueError as e:

            print("\n+==================================================+")
            print("> !ATTENTION! <")
            print("The file integrity check failed!")
            print("This means that the file downloaded is corrupted or damaged in some way.")
            print("Your current file (if one is targeted) has not been altered.")
            print("\nThere are many different causes for this error to occur.")
            print("It is likely that this is a one-off event.")
            print("Try again, and if this command continues to fail,")
            print("then your network or storage device might have a problem.")

            error_report(e)

            return False

        except Exception as e:

            self._url_report("File Download")

            # Report the error

            error_report(e)

            return False

        if self.integrity:

            output("# Integrity test passed!")

        output("# Saved file to: {}".format(path))

        if not args.batch:

            output("\n[ --== Download Complete! ==-- ]")

        if args.batch:

            output("# Download complete!")

        # Determining output name:

        target = self.fileutil.path

        # No output name defined via argument or path:

        if output_name is None and self.fileutil.path.is_dir():

            # Keep original name:

            target = self.fileutil.path / path.name

        # Output name specified via argument but not path:

        elif output_name is not None and self.fileutil.path.is_dir():

            # Save file with custom name:

            target = self.fileutil.path / output_name

        # Output name specified via argument and path:

        elif output_name is not None and self.fileutil.path.is_file():

            # Save file with custom name other than filename in path:

            target = self.fileutil.path.parent / output_name

        # Downloading file:

        val = self.fileutil.install(path, target, backup=backup, new=new, target_copy=target_copy)

        if not val:

            # Download process failed

            return

        # Cleaning up temporary directory:

        output("\n# Cleaning up temporary directory...")

        self.fileutil.close_temp_dir()

        output("# Done cleaning temporary directory!")

        output("\n# Update complete!")

        # Updating values

        self.version = ver

        self.buildnum = build

        return val


    def _select(self, val, choice, default, name, print_output=True):
        """
        Select a value from choices.
        Special values:
          - '', uses default
          - -1 or 'latest', picks newest automatically
          - 'current', uses currently installed version/build
        Robust to string/int mismatches and list ordering.
        """

        # Normalize blank -> default

        if val == '':

            val = default

        # Normalize numeric sentinel for latest

        if val == -1:

            val = 'latest'

        # Normalize strings

        if isinstance(val, str):

            s = val.strip().lower()

            if s == 'latest':

                val = 'latest'

            elif s == 'current':

                val = 'current'

            else:

                # If choices are ints and user typed digits, coerce

                if choice and isinstance(choice[0], int) and s.isdigit():

                    val = int(s)

        # Handle “latest”

        if val == 'latest':

            if not choice:

                if print_output:

                    output(f"\n# Error: No {name}s available!")

                return None

            # If this is build selection, take the numeric max (most robust).

            if name in ('build', 'buildnum'):

                # Coerce to ints if needed

                if isinstance(choice[0], str):

                    try:

                        nums = [int(x) for x in choice]

                    except ValueError:

                        # Fallback: keep original and rely on last element

                        latest = choice[-1]

                    else:

                        latest = max(nums)

                else:

                    latest = max(choice)

                if print_output:

                    output(f"# Selecting latest {name} - [{latest}] ...")

                return latest

            # For versions, keep your existing “newest” behavior (last element).

            latest = choice[-1]

            if print_output:

                output(f"# Selecting latest {name} - [{latest}] ...")

            return latest

        # Handle “current”

        if val == 'current':

            if name == 'version':

                val = self.version

            elif name in ('build', 'buildnum'):

                val = self.buildnum

        # Coerce for membership checks

        if choice:

            if isinstance(choice[0], int) and isinstance(val, str) and val.isdigit():

                val = int(val)

            elif isinstance(choice[0], str) and not isinstance(val, str):

                val = str(val)

        # Validate

        if val not in choice:

            if print_output:

                output(f"\n# Error: Invalid {name} selected!")

            return None

        if print_output:

            output(f"# Selecting {name}: [{val}] ...")

        return val


    def _url_report(self, point: str):
        """
        Reports an error during a request operation.
        :param point: Point of failure
        :type point: str
        """

        print("\n+==================================================+")
        print("> !ATTENTION! >")
        print("An error occurred during a request operation.")
        print("Fail Point: {}".format(point))
        print("Your check/update operation will be canceled.")
        print("Detailed error info below:")        


if __name__ == '__main__':

    # Ran as script

    check_internet_connection()

    parser = argparse.ArgumentParser(description='PaperMC Server Updater.', epilog='Please check the github page for more info: https://github.com/Creeper36/PaperMC-Update.')

    parser.add_argument('path', help='Path to paper jar file', default=Path(__file__).expanduser().resolve().absolute().parent, type=Path, nargs='?')

    version = parser.add_argument_group('Version Options', 'Arguments for selecting and altering server version information')

    # +===========================================+
    # Server version arguments:

    version.add_argument('-v', '--version', help='Server version to download(Sets default value)', default='latest', type=str)
    version.add_argument('-b', '--build', help='Server build to download(Sets default value)', default=-1, type=int)
    version.add_argument('-iv', help='Sets the currently installed server version, ignores config', default='0', type=str)
    version.add_argument('-ib', help='Sets the currently installed server build, ignores config', default=0, type=int)
    version.add_argument('-sv', '--server-version', help="Displays server version from configuration file and exits", action='store_true')

    # +===========================================+
    # File command line arguments:

    file = parser.add_argument_group("File Options", "Arguments for altering how we work with files")
    file.add_argument('-nlc', '--no-load-config', help='Will not load Paper config file: version_history.json', action='store_false')
    file.add_argument('-cf', '--config-file', help='Path to Paper config file to read from, usually version_history.json - DEFAULTS to [SERVER_JAR_DIR]/version_history.json')
    file.add_argument('-nb', '--no-backup', help='Disables backup of the old server jar', action='store_true')
    file.add_argument('-n', '--new', help='Downloads a new paper jar instead of updating. Great for configuring a new server install', action='store_true')
    file.add_argument('-o', '--output', help='Name of the new file')
    file.add_argument('-co', '--copy-old', help='Copies the old file to a new location')
    file.add_argument('-ni', '--no-integrity', help='Skips the file integrity check', action='store_false')

    # +===========================================+
    # General command line arguments:

    parser.add_argument('-c', '--check-only', help='Checks for an update, does not download', action='store_true')
    parser.add_argument('-nc', '--no-check', help='Does not check for an update, skips to download', action='store_true')
    parser.add_argument('-i', '--interactive', help='Prompts the user for the paper.jar version they would like to download', action='store_true')
    parser.add_argument('-q', '--quiet', help="Will only output errors and interactive questions to the terminal", action='store_true')
    parser.add_argument('-s', '--stats', help='Displays statistics on the selected version and build', action='store_true')
    parser.add_argument('-ba', '--batch', help='Log-friendly output mainly for batch scripts', action='store_true')
    parser.add_argument('-V', '--script-version', help='Displays script version', version=__version__, action='version')
    parser.add_argument("-ua", "--user-agent", help="User agent to utilize when making requests this should be unique and custom to you! See https://docs.papermc.io/misc/downloads-api/", type=str, default='')
    parser.add_argument('-u', '--upgrade', help='Upgrades this script to a new version if necessary, and exits', action='store_true')
    parser.add_argument('-F', '--force-upgrade', help='Force a script upgrade even if versions match (implies --upgrade)', action='store_true')

    # +===========================================+
    # Deprecated arguments - Included for compatibility, but do nothing

    parser.add_argument('-ndc', '--no-dump-config', help=argparse.SUPPRESS, action='store_false')
    parser.add_argument('--config', help=argparse.SUPPRESS, default='NONE')
    parser.add_argument('-C', '--cleanup', help=argparse.SUPPRESS, action='store_true')
    parser.add_argument('-nr', '--no-rename', help=argparse.SUPPRESS)

    args = parser.parse_args()

    def _bind_output_with_args(_args):
        global output
        _orig_output = output
        def _bound_output(text, args=None):
            return _orig_output(text, _args if args is None else args)
        output = _bound_output

    _bind_output_with_args(args)

    
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

    serv = ServerUpdater(args.path, config_file=args.config_file, config=args.no_load_config or args.server_version, prompt=args.interactive,
                         version=args.iv, build=args.ib, integrity=args.no_integrity, user_agent=args.user_agent)

    update_available = True

if args.check_only:

    output("\n[ --== Checking For New Version: ==-- ]\n")

    # Load version info using same logic as interactive

    local_version, local_build = serv.fileutil.load_config(serv.config_file)

    # Show Local version info (stats-style block)

    output("\n+==========================================================================+")
    output("# Local Server Version Information:")
    output(f"  > Version: [{local_version}]")
    output(f"  > Build:   [{local_build}]")
    output("+==========================================================================+")

    # Compare with remote builds

    try:

        remote_builds = serv.update.get_buildnums(local_version)

    except Exception as e:

        error_report(e, net=isinstance(e, URLError))

        sys.exit(0)

    if not remote_builds:

        output(f"# ERROR: No builds found for version {local_version}")

        sys.exit(0)

    latest_remote_build = max(remote_builds)

    # Show Remote version info (stats-style block)

    output("\n+==========================================================================+")
    output("# Remote Server Version Information:")
    output(f"  > Version: [{local_version}]")
    output(f"  > Build:   [{latest_remote_build}]")
    output("+==========================================================================+\n")

    if local_build >= latest_remote_build:

        output("# You are up to date!")

    else:

        output(f"# New Version available! - [Version: {local_version}.{latest_remote_build}]")

    output("\n[ --== Version check complete! ==-- ]\n")

    sys.exit(0)


    # Determine if we should upgrade:

    if args.force_upgrade:

        output("# Force upgrade enabled!")

    if args.upgrade or args.force_upgrade:

        output("# Checking for script upgrade ...")

        upgrade_script(serv, force=args.force_upgrade)

        sys.exit(0)

    # Start the server updater

    serv.start()

    # Figure out the output name:

    name = None

    if args.output:

        # Name was explicitly given to us:

        name = args.output

    elif args.path.is_file():

        # Get filename from the given path:

        name = args.path.name

    # Check if we are just looking for server info:

    if args.server_version:

        # Already printed it, lets exit

        sys.exit(0)

    # Check for displaying stats:

    if args.stats:

        # Display stats to the terminal:

        serv.view_data()

        sys.exit(0)

    # Checking if we are skipping the update

    if not args.no_check and not args.new and not args.interactive:

        # Allowed to check for update:

        update_available = serv.check(args.version, args.build)

    # Checking if we can download:

    if not args.check_only and update_available:

        # Allowed to download/Can download

        serv.get_new(default_version=args.version, default_build=args.build, backup=not (args.no_backup or args.new),
                    new=args.new, output_name=name, target_copy=args.copy_old)

        sys.exit(1)

    else:

        sys.exit(0)

