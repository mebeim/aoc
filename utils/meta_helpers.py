def seconds_to_most_relevant_unit(s):
	s *= 1e6
	if s < 1000: return '{:.3f}µs'.format(s)

	s /= 1000
	if s < 1000: return '{:.3f}ms'.format(s)

	s /= 1000
	if s < 60: return '{:.3f}s'.format(s)

	s /= 60
	return '{:d}m {:.3f}s'.format(int(s), s/60%60)
