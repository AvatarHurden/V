## Installation

Clone the repository and cd into the directory

```
git clone https://github.com/AvatarHurden/V
cd V
``` 

For the most recent development version, switch to the develop branch.

```
git checkout develop
``` 

To build the project, run the following command.

```
msbuild V.sln
```

### macOS/Unix

To run msbuild, it is necessary to install the Mono framework.

### Windows

To use the command-line program msbuild, it is necessary to download the [build tools](https://www.visualstudio.com/downloads/#build-tools-for-visual-studio-2017).

## Running

After compilation, cd into the correct folder.

```
cd V/bin/Debug
```

### Windows

Simply run the executable

```
V.exe --help
```

### macOS/UNIX

Run mono with the program as an argument

```
mono V.exe --help
```
