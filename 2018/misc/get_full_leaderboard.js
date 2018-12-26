function getFullLeaderboard(excludedDays=[]) {
	return new Promise(resolve => {
		let users = {}

		function getDay(d) {
			if (!excludedDays.includes(d)) {
				console.log(`Fetching day ${d}.`)

				fetch(`https://adventofcode.com/2018/leaderboard/day/${d}`).then(resp => {
					resp.text().then(text => {
						let html    = (new DOMParser).parseFromString(text, 'text/html'),
						    entries = html.getElementsByClassName('leaderboard-entry'),
						    todayUsers = {}


						for (let e of entries) {
							let score    = 101 - parseInt(e.querySelector('.leaderboard-position').textContent),
							    aocpp    = e.querySelector('.supporter-badge'),
							    sponsor  = e.querySelector('.sponsor-badge'),
							    anon     = e.querySelector('.leaderboard-anon'),
							    image    = e.querySelector('.leaderboard-userphoto > img'),
							    link     = null,
    						    username = null

							if (aocpp)
								e.removeChild(aocpp)

							if (sponsor)
								e.removeChild(sponsor)

							link = e.querySelector('a')

							if (anon) {
								username = `(anon ${anon.textContent.match(/#\d+/)[0]})`
							} else {
								if (link) {
									username = link.textContent
								} else {
									while (e.children.length)
										e.removeChild(e.children[0])

									username = e.textContent.trim()
								}
							}

							let key = username + (link ? link.href : '') + (image ? image.src : '')

							if (todayUsers[key]) {
								todayUsers[key].score += score
								todayUsers[key].times += 1
							} else {
								todayUsers[key] = {username, score, times: 1}

								if (link)
									todayUsers[key].link = link.href
							}
						}

						for (let k of Object.keys(todayUsers)) {
							let user = todayUsers[k]

							if (users[k]) {
								users[k].score += user.score
								users[k].times += user.times
								users[k].days += 1
							} else {
								users[k] = {
									username: user.username,
									score: user.score,
									times: user.times,
									days: 1
								}

								if (user.link)
									users[k].link = user.link
							}
						}
					})
				})
			} else {
				console.log(`Skipping excluded day ${d}.`)
			}

			if (d < 25) {
				getDay(d + 1)
			} else if (d == 25) {
				console.log('Done.')
				resolve(users)
			}
		}

		getDay(1)
	})
}

getFullLeaderboard([6]).then(l => window.l = l)

// Run after getFullLeaderBoard has finished.
(leaderboard =>  {
	console.log('Generating leaderboard Markdown.')

	let sorted = Object.keys(leaderboard).map(name => leaderboard[name])

	sorted.sort((b, a) => a.score - b.score)

	let md = 'Rank | User | Score | Times (days) on leaderboard\n'
		md += '-|-|-|-\n'

	let rank = 0, lastScore = -1, acc = 1

	for (let user of sorted) {
		let username = user.link ? `[${user.username}](${user.link})` : `${user.username}`

		if (user.score != lastScore) {
			rank += acc
			acc = 1
		} else {
			acc++
		}

		md += `${rank} | ${username} | ${user.score} | ${user.times} (${user.days})\n`

		lastScore = user.score
	}

	copy(md)

	console.log('Leaderboard copied to clipboard.')
})(l)
