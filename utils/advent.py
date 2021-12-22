import os
import sys
import re
from importlib import find_loader
from datetime import datetime, timedelta
from time import sleep

def log(s, *a):
	sys.stderr.write('[advent] ' + s.format(*a))
	sys.stderr.flush()

def logcont(s, *a):
	sys.stderr.write(s.format(*a))
	sys.stderr.flush()

def check_or_die(resp):
	if resp.status_code != 200:
		logcont('\n')
		log('ERROR: response {}, url: {}\n', resp.status_code, resp.url)
		log('Did you log in and update your session cookie?\n')
		sys.exit(1)

	if 'please identify yourself' in resp.text.lower():
		logcont('\n')
		log('ERROR: Server returned 200, but is asking for identification.\n')
		log('Did you log in and update your session cookie?\n')
		sys.exit(1)

def check_setup_once():
	if YEAR == -1 and DAY == -1:
		now = datetime.utcnow() + timedelta(hours=-5)
		y, m, d = now.year, now.month, now.day

		if m != 12 or (m == 12 and d > 25):
			log('ERROR: year and day not set, and no event currently running!\n')
			sys.exit(1)

		log('Year and day not set, assuming today: Dec {}, {}.\n', d, y)
		setup(y, d)

def setup(year, day):
	global YEAR
	global DAY
	global SESSION

	if not (year >= 2015 and 1 <= day <= 25):
		log('ERROR: invalid year and/or day set!\n')
		sys.exit(1)

	YEAR = year
	DAY  = day

	if REQUESTS and os.path.isfile('secret_session_cookie'):
		with open('secret_session_cookie') as f:
			SESSION = f.read().rstrip()
			S.cookies.set('session', SESSION)

def get_input(fname=None, mode='r'):
	check_setup_once()

	if fname is not None:
		return open(fname, mode)

	if not os.path.isdir(CACHE_DIR):
		try:
			os.mkdir(CACHE_DIR)
			log("Created cache directory '{}' since it did not exist.\n", CACHE_DIR)
		except Exception as e:
			log("ERROR: could not create cache directory '{}'.\n", CACHE_DIR)
			log('{}\n', str(e))
			sys.exit(1)

	log('Getting input for year {} day {}... ', YEAR, DAY)
	fname = os.path.join(CACHE_DIR, '{}_{:02d}.txt'.format(YEAR, DAY))

	try:
		file = open(fname, mode)
		logcont('done (from disk).\n')
		return file
	except FileNotFoundError:
		pass

	if not REQUESTS:
		logcont('err!\n')
		log('ERROR: cannot download input, no requests module installed!\n')
		sys.exit(1)
	elif not SESSION:
		logcont('err!\n')
		log('ERROR: cannot download input file without session cookie!\n')
		sys.exit(1)

	logcont('downloading... ')

	r = S.get(URL.format(YEAR, DAY, 'input'))
	check_or_die(r)

	with open(fname, 'wb') as f:
		f.write(r.content)

	file = open(fname, mode)
	logcont('done.\n')

	return file

def print_answer(part, answer):
	print('Part {}:'.format(part), answer)

def submit_answer(part, answer):
	check_setup_once()

	if not REQUESTS:
		log('Cannot upload answer, no requests module installed!\n')
		print_answer(part, answer)
		return False

	log('Submitting day {} part {} answer: {}\n', DAY, part, answer)

	r = S.post(URL.format(YEAR, DAY, 'answer'), data={'level': part, 'answer': answer})
	check_or_die(r)
	t = r.text.lower()

	if 'did you already complete it' in t:
		log('Already completed or wrong day/part.\n')
		return False

	if "that's the right answer" in t:
		matches = re.findall(r'rank\s+(\d+)', t)
		if matches:
			logcont('Right answer! Rank {}.\n', matches[0])
		else:
			log('Right answer!\n')

		if DAY == 25 and part == 1:
			log("It's Christmas! Automatically submitting second part in 5s...\n")
			sleep(5)
			S.post(URL.format(YEAR, 25, 'answer'), data={'level': 2, 'answer': 0})
			logcont('done!\n')
			log('Go check it out: https://adventofcode.com/{}/day/25#part2\n', YEAR)

		return True

	if 'you have to wait' in t:
		matches = re.compile(r'you have ([\w ]+) left to wait').findall(t)

		if matches:
			log('Submitting too fast, {} left to wait.\n', matches[0])
		else:
			log('Submitting too fast, slow down!\n')

		return False

	log('Wrong answer :(\n')
	return False

URL       = 'https://adventofcode.com/{:d}/day/{:d}/{:s}'
SESSION   = ''
CACHE_DIR = '../inputs'
YEAR      = -1
DAY       = -1
REQUESTS  = find_loader('requests')

if REQUESTS:
	import requests
	S = requests.Session()
