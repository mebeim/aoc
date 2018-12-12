#!/usr/bin/env python3

import os
import sys
import platform
from datetime import datetime, timedelta

def log(s, *a):
	sys.stderr.write(s.format(*a))
	sys.stderr.flush()

def read_n_close(fname):
	with open(fname) as f:
		return f.read().rstrip()

def check_or_die(resp):
	if resp.status_code != 200:
		log('\n[utils] ERROR: response {}, url: {}\n', resp.status_code, resp.url)

		if resp.status_code == 500:
			log('[utils] Did you log in and update your session cookie?\n')

		sys.exit(1)

def check_setup_once():
	global YEAR
	global DAY

	if YEAR == -1 and DAY == -1:
		now = datetime.utcnow() + timedelta(hours=-5)
		y, m, d = now.year, now.month, now.day

		if m != 12 or (m == 12 and d > 25):
			log('[utils] ERROR: year and day not set, and no event currently running!')
			sys.exit(1)

		log('[utils] Year and day not set, assuming today: Dec {}, {}.\n', d, y)
		setup(y, d)

def setup(year, day, dry_run=False):
	global YEAR
	global DAY
	global DRY_RUN
	global SESSION

	assert year >= 2015
	assert 1 <= day <= 25

	YEAR    = year
	DAY     = day
	DRY_RUN = dry_run

	if not PYPY and os.path.isfile('secret_session_cookie'):
		with open('secret_session_cookie') as f:
			SESSION = f.read().rstrip()
			s.cookies.set('session', SESSION)

def get_input(fname=None, mode='r'):
	check_setup_once()
	log('[utils] Getting input for year {} day {}... ', YEAR, DAY)

	if fname is None:
		fname = os.path.join(CACHE_DIR, '{}_{:02d}.txt'.format(YEAR, DAY))

	if not os.path.isfile(fname):
		if PYPY:
			log('[utils] ERROR: cannot download input running with PyPy, use CPython!\n')
			sys.exit(1)

		if SESSION:
			log('downloading... ')

			r = s.get(URL.format(YEAR, DAY, 'input'))
			check_or_die(r)

			with open(fname, 'wb') as f:
				f.write(r.content)

			log('done.\n')
		else:
			log('err!\n')
			log('[utils] ERROR: cannot download input file without session cookie!\n')
			sys.exit(1)
	else:
		log('done (from disk).\n')

	return open(fname, mode)

def submit_answer(level, answer):
	check_setup_once()

	if DRY_RUN:
		print('Level {}: {}'.format(level, answer))
	elif PYPY:
		log('[utils] Cannot upload answer running with PyPy, use CPython!\n')
		print('Level {}: {}'.format(level, answer))
	else:
		log('[utils] Submitting day {} level {} answer: {}\n', DAY, level, answer)

		r = s.post(URL.format(YEAR, DAY, 'answer'), data={'level': level, 'answer': answer})
		check_or_die(r)

		t = r.text.lower()

		if 'did you already complete it' in t:
			log('[utils] Already completed!\n')
			return True

		if "that's the right answer" in t:
			log('[utils] Right answer!\n')
			return True

		if 'you have to wait' in t:
			log('[utils] Submitting too fast, slow down!')
			return False

		log('[utils] Wrong answer :(\n')
		return False

URL       = 'https://adventofcode.com/{:d}/day/{:d}/{:s}'
SESSION   = ''
CACHE_DIR = './inputs'
YEAR      = -1
DAY       = -1
DRY_RUN   = False
PYPY      = platform.python_implementation() == 'PyPy'

if not PYPY:
	import requests

	s = requests.Session()
