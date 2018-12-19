Generate a video animation of the evolution over time of the field described by the given input file. Using PyPy3 for the `generate_data.py` script is recommended since it runs way faster than with CPython. [Youtube video](https://www.youtube.com/watch?v=OVt5xOF19cQ).

	$ ./generate_data.py example.in Nframes
	$ ./generate_animation.py

Using Python + PIL for this kind of stuff is probably insane, but you know... I like it the hard way. Sprites were found on opengameart.org and then carefully edited by me by hand using Gimp (thanks to my best friend Mattyw for helping me with this part).

Also, `ffmpeg` is *a real pain in the ass* when it comes to choosing an appropriate frame rate and duration of images. Had to hack it like this to generate an increasingly faster video:

	ffmpeg -ss 0.0 -t 0.2 -i animation.mp4 -filter:v "setpts=25*PTS" animation_p1.mp4
	ffmpeg -ss 0.2 -t 0.4 -i animation.mp4 -filter:v "setpts=12*PTS" animation_p2.mp4
	ffmpeg -ss 0.6 -t 0.8 -i animation.mp4 -filter:v "setpts=5*PTS" animation_p3.mp4
	ffmpeg -ss 1.4 -t 0.6 -i animation.mp4 -filter:v "setpts=2*PTS" animation_p4.mp4
	ffmpeg -ss 2.0 -i animation.mp4 animation_p5.mp4

	for f in animation_p*.mp4; do echo "file '$f'" >> list.txt; done

	ffmpeg -f concat -i list.txt -c copy final.mp4
