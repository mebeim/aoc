import os
import sys
import re

from importlib import find_loader
from datetime import datetime, timedelta

from .helpers import log

def check_or_die(resp):
	pls_identify = 'please identify yourself' in resp.text.lower()

	if resp.status_code != 200:
		log('\n[advent] ERROR: response {}, url: {}\n', resp.status_code, resp.url)
		log('[advent] Did you log in and update your session cookie?\n')
		sys.exit(1)
	elif pls_identify:
		log('\n[advent] ERROR: Server returned 200, but is asking for identification.\n')
		log('[advent] Did you log in and update your session cookie?\n')
		sys.exit(1)

def check_setup_once():
	if YEAR == -1 and DAY == -1:
		now = datetime.utcnow() + timedelta(hours=-5)
		y, m, d = now.year, now.month, now.day

		if m != 12 or (m == 12 and d > 25):
			log('[advent] ERROR: year and day not set, and no event currently running!\n')
			sys.exit(1)

		log('[advent] Year and day not set, assuming today: Dec {}, {}.\n', d, y)
		setup(y, d)

def setup(year, day):
	global YEAR
	global DAY
	global SESSION

	assert year >= 2015
	assert 1 <= day <= 25

	YEAR = year
	DAY  = day

	if REQUESTS and os.path.isfile('secret_session_cookie'):
		with open('secret_session_cookie') as f:
			SESSION = f.read().rstrip()
			s.cookies.set('session', SESSION)

def get_input(fname=None, mode='r'):
	check_setup_once()

	if not os.path.isdir(CACHE_DIR):
		try:
			os.mkdir(CACHE_DIR)
			log("[advent] Created cache directory '{}' since it did not exist.\n", CACHE_DIR)
		except Exception as e:
			log("[advent] ERROR: could not create cache directory '{}'.\n", CACHE_DIR)
			log('[advent] {}\n', str(e))
			sys.exit(1)

	log('[advent] Getting input for year {} day {}... ', YEAR, DAY)

	if fname is None:
		fname = os.path.join(CACHE_DIR, '{}_{:02d}.txt'.format(YEAR, DAY))

	if not os.path.isfile(fname):
		if not REQUESTS:
			log('err!\n')
			log('[advent] ERROR: cannot download input, no requests module installed!\n')
			sys.exit(1)
		elif not SESSION:
			log('err!\n')
			log('[advent] ERROR: cannot download input file without session cookie!\n')
			sys.exit(1)

		log('downloading... ')

		r = s.get(URL.format(YEAR, DAY, 'input'))
		check_or_die(r)

		with open(fname, 'wb') as f:
			f.write(r.content)

		log('done.\n')

	else:
		log('done (from disk).\n')

	return open(fname, mode)

def print_answer(part, answer):
	print('Part {}:'.format(part), answer)

def submit_answer(part, answer):
	check_setup_once()

	if not REQUESTS:
		log('[advent] Cannot upload answer, no requests module installed!\n')
		print_answer(part, answer)
		return True

	log('[advent] Submitting day {} part {} answer: {}\n', DAY, part, answer)

	r = s.post(URL.format(YEAR, DAY, 'answer'), data={'level': part, 'answer': answer})
	check_or_die(r)
	t = r.text.lower()

	if 'did you already complete it' in t:
		log('[advent] Already completed!\n')
		return True

	if "that's the right answer" in t:
		log('[advent] Right answer!\n')
		return True

	if 'you have to wait' in t:
		matches = re.compile(r'you have ([\w ]+) left to wait').findall(t)

		if matches:
			log('[advent] Submitting too fast, {} left to wait.\n', matches[0])
		else:
			log('[advent] Submitting too fast, slow down!\n')

		return False

	log('[advent] Wrong answer :(\n')
	return False

URL       = 'https://adventofcode.com/{:d}/day/{:d}/{:s}'
SESSION   = ''
CACHE_DIR = '../inputs'
YEAR      = -1
DAY       = -1
REQUESTS  = find_loader('requests')

if REQUESTS:
	import requests
	s = requests.Session()
