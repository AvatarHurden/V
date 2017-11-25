To compile this documentation, the ```lib``` folder must be added to your TEXMFHOME.

To discover the location of this folder in your system, execute the command

```
kpsewhich -var-value=TEXMFHOME
```

Most likely, this will indicate a folder that does not exist yet in your system.

Create this folder and, within it , the folder ```tex\latex```.
Add the ```lib``` folder to this new folder and run the following command:

```
texhash .
```

This will add the style files to your tex path and will allow compilation of the document.
