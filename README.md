1. ## Installation

Clone the repository and ```cd``` into the directory

```
git clone https://github.com/AvatarHurden/V
cd V
```

For the most recent development version, switch to the develop branch.

```
git checkout develop
```

2. ## Building

  - ### Visual Studio

Open the ```V.sln``` project file in Visual Studio to compile and run the code.

  - ### Command Line

To build the project in the command line, run the following command.

```
msbuild V.sln
```

#### macOS/Unix

To run ```msbuild```, it is necessary to install the [Mono framework](http://www.mono-project.com/download/stable/).

#### Windows

To use the command-line program ```msbuild```, it is necessary to download the [build tools](https://www.visualstudio.com/downloads/#build-tools-for-visual-studio-2017).

3. ## Running

After compilation, ```cd``` into the correct folder.

```
cd V/bin/Debug
```

  - ### Windows

Simply run the executable

```
V.exe --help
```

  - ### macOS/Unix

Run mono with the program as an argument

```
mono V.exe --help
```
