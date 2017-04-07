---
title: Notes on Homework 2
---

([Go back to the course page](/classes/parp/index.html))

With a few edits, it is possible to turn your simulation into a video. I found this useful for debugging -- sometimes it is easier to "see" what is wrong than try to trace the code. :)

Here is an example:

<video width="640" height="480" controls>
  <source src="/raw/parp/hw2/test-05.mp4" type="video/mp4">
Your browser does not support the video tag.
</video> 

Here are the steps I used to do this. These steps assume you're using a unix-like.

1. Edit your particle program so that on each time step, the coordinates of all points are written out to a file -- one for each step. Here's how I did it: toward the top of ``main`` (and before the main loop) I declared a string, ``outname``, to hold the title of the output file.

    ```c
    char *outname = (char*) malloc(32 * sizeof(char));
    ```

2. Toward the end of the loop, write the coordinates to a file. This did it for me. You may need to create the ``out`` directory before running the program, I don't remember. That ``sprintf`` command writes the name of the output file to the string we declared earlier; the ``%05d`` pads ``step`` to length 5. This is necessary to make later processing steps work.

    ```c
    sprintf( outname, "out/fout-%05d.txt", step );``
    FILE *fout = fopen( outname, "w" );``
    save( fout, n, particles);``
    fclose( fout );``
    ```

3. If everything went well, when you run your program now (say by making the ``job-stampede-*`` script executable, or by running the program directly) it will populate the ``out`` subdirectory with a bunch of text files called ``fout-00000.txt``, ``fout-00001.txt``, and so on. These are the coordinates of the particles at each time step, in order.

4. On your local machine, put the following script into a text file called ``particles.sh``. **Important:** Before running this, you will need to replace ``USERNAME`` with your *stampede* username, and ``PATH`` with the path to the directory where ``out`` lives on stampede. To find these values you can use ``whoami`` (to get your username) and then cd to the directory where ``out`` lives and say ``pwd``.

    What this script does is (1) download all those ``fout-`` text files with ``scp``, (2) convert each file to a png with ``gnuplot``, and (3) stitch the png files into an mp4 with ``ffmpeg``. (Did I mention you need to have ``gnuplot`` and ``ffmpeg``? You do.) Note that ``ffmpeg`` will automatically put the frames in the right order, since we padded our filenames to the same length. Woo!

    ```bash
    #!/bin/bash
    
    scp -r USERNAME@stampede.tacc.utexas.edu:/PATH/out .
    
    (
    cd out
    
    for FILE in *.txt; do
      gnuplot <<- EOF
        set terminal png
        set output "${FILE}.png"
        plot "${FILE}" notitle pointtype 6
    EOF
    done
    
    ffmpeg -r 60 -f image2 -s 1080x960 -i 'fout-%05d.txt.png' -vcodec libx264 -crf 25 -pix_fmt yuv420p test.mp4
    
    rm *.png
    )
    ```

If everything went well, when you run this command you will be prompted for your stampede password and the rest requires no intervention. After a few minutes you should have an mp4 video that looks something like the above example.
