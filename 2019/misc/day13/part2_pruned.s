     0:  000 02     mul          [380]          [379]          [385]
     4:  010 08     eq          [2751]        576818           [381]
     8:  010 05     jnz          [381]            12
    11:  000 99     hlt
    12:  001 09     rel          2752
    14:  011 01     add             0              0           [383]
    18:  011 02     mul             1              0           [382]
    22:  201 01     add             0           [382]          [r+1]
    26:  210 01     add          [383]             0           [r+2]
    30:  211 02     mul             1             37           [r+0]
    34:  011 06     jz              0            578
    37:  000 04     out          [382]
    39:  000 04     out          [383]
    41:  002 04     out          [r+1]
    43:  010 01     add          [382]             1           [382]
    47:  010 07     lt           [382]            44           [381]
    51:  010 05     jnz          [381]            22
    54:  010 01     add          [383]             1           [383]
    58:  010 07     lt           [383]            24           [381]
    62:  010 05     jnz          [381]            18
    65:  010 06     jz           [385]            69
    68:  000 99     hlt
    69:  001 04     out            -1
    71:  001 04     out             0
    73:  000 04     out          [386]
    75:  000 03     in           [384]
    77:  010 07     lt           [384]             0           [381]
    81:  010 05     jnz          [381]            94
    84:  001 07     lt              0           [384]          [381]
    88:  010 05     jnz          [381]           108
    91:  011 06     jz              0            161
    94:  001 07     lt              1           [392]          [381]
    98:  010 06     jz           [381]           161
   101:  011 01     add             0             -1           [384]
   105:  011 06     jz              0            119
   108:  010 07     lt           [392]            42           [381]
   112:  010 06     jz           [381]           161
   115:  011 01     add             1              0           [384]
   119:  210 02     mul          [392]             1           [r+1]
   123:  211 02     mul            22              1           [r+2]
   127:  211 01     add             0              0           [r+3]
   131:  211 02     mul             1            138           [r+0]
   135:  011 05     jnz             1            549
   138:  000 01     add          [392]          [384]          [392]
   142:  210 02     mul          [392]             1           [r+1]
   146:  211 01     add             0             22           [r+2]
   150:  211 01     add             3              0           [r+3]
   154:  211 02     mul             1            161           [r+0]
   158:  011 06     jz              0            549
   161:  011 02     mul             0              1           [384]
   165:  200 01     add          [388]          [390]          [r+1]
   169:  210 01     add          [389]             0           [r+2]
   173:  211 02     mul             1            180           [r+0]
   177:  011 06     jz              0            578
   180:  012 06     jz           [r+1]           213
   183:  012 08     eq           [r+1]             2           [381]
   187:  010 06     jz           [381]           205
   190:  200 01     add          [388]          [390]          [r+1]
   194:  201 02     mul             1           [389]          [r+2]
   198:  211 02     mul           205              1           [r+0]
   202:  011 05     jnz             1            393
   205:  010 02     mul          [390]            -1           [390]
   209:  011 01     add             0              1           [384]
   213:  210 02     mul          [388]             1           [r+1]
   217:  200 01     add          [389]          [391]          [r+2]
   221:  211 02     mul           228              1           [r+0]
   225:  011 06     jz              0            578
   228:  012 06     jz           [r+1]           261
   231:  012 08     eq           [r+1]             2           [381]
   235:  010 06     jz           [381]           253
   238:  201 02     mul             1           [388]          [r+1]
   242:  200 01     add          [389]          [391]          [r+2]
   246:  211 02     mul           253              1           [r+0]
   250:  011 06     jz              0            393
   253:  010 02     mul          [391]            -1           [391]
   257:  011 01     add             0              1           [384]
   261:  010 05     jnz          [384]           161
   264:  200 01     add          [388]          [390]          [r+1]
   268:  200 01     add          [389]          [391]          [r+2]
   272:  211 01     add             0            279           [r+0]
   276:  011 05     jnz             1            578
   279:  012 06     jz           [r+1]           316
   282:  012 08     eq           [r+1]             2           [381]
   286:  010 06     jz           [381]           304
   289:  200 01     add          [388]          [390]          [r+1]
   293:  200 01     add          [389]          [391]          [r+2]
   297:  211 01     add           304              0           [r+0]
   301:  011 06     jz              0            393
   304:  010 02     mul          [390]            -1           [390]
   308:  010 02     mul          [391]            -1           [391]
   312:  011 01     add             0              1           [384]
   316:  010 05     jnz          [384]           161
   319:  201 02     mul             1           [388]          [r+1]
   323:  210 02     mul          [389]             1           [r+2]
   327:  211 02     mul             1              0           [r+3]
   331:  211 02     mul             1            338           [r+0]
   335:  011 06     jz              0            549
   338:  000 01     add          [388]          [390]          [388]
   342:  000 01     add          [389]          [391]          [389]
   346:  210 02     mul          [388]             1           [r+1]
   350:  210 01     add          [389]             0           [r+2]
   354:  211 01     add             4              0           [r+3]
   358:  211 02     mul           365              1           [r+0]
   362:  011 05     jnz             1            549
   365:  010 07     lt           [389]            23           [381]
   369:  010 05     jnz          [381]            75
   372:  001 04     out            -1
   374:  001 04     out             0
   376:  001 04     out             0
   378:  000 99     hlt
   379:  000 00     (bad)
   380:  000 01     add            [0]            [0]            [0]
   384:  000 00     (bad)
   385:  000 00     (bad)
   386:  000 00     (bad)
   387:  003 04     out            20
   389:  000 19     (bad)
   390:  000 01     add            [1]           [22]          [109]
   394:  000 03     in         [22102]
   396:  000 01     add           [-2]            [1]        [21201]
   400:  -01 99     hlt
   401:  000 00     (bad)
   402:  000 02     mul        [21101]            [0]            [0]
   406:  000 03     in         [21101]
   408:  004 14     (bad)
   409:  000 00     (bad)
   410:  000 00     (bad)
   411:  011 06     jz              0            549
   414:  212 02     mul          [r-2]             1           [r+1]
   418:  221 01     add             0           [r-1]          [r+2]
   422:  211 01     add           429              0           [r+0]
   426:  011 06     jz              0            601
   429:  012 01     add          [r+1]             0           [435]
   433:  000 01     add          [386]            [0]          [386]
   437:  001 04     out            -1
   439:  001 04     out             0
   441:  000 04     out          [386]
   443:  010 01     add          [387]            -1           [387]
   447:  010 05     jnz          [387]           451
   450:  000 99     hlt
   451:  001 09     rel            -3
   453:  021 06     jz              0           [r+0]
   456:  001 09     rel             8
   458:  222 02     mul          [r-7]          [r-6]          [r-3]
   462:  222 01     add          [r-3]          [r-5]          [r-3]
   466:  212 02     mul          [r-4]            64           [r-2]
   470:  022 07     lt           [r-3]          [r-2]          [381]
   474:  010 05     jnz          [381]           492
   477:  212 02     mul          [r-2]            -1           [r-1]
   481:  222 01     add          [r-3]          [r-1]          [r-3]
   485:  022 07     lt           [r-3]          [r-2]          [381]
   489:  010 06     jz           [381]           481
   492:  212 02     mul          [r-4]             8           [r-2]
   496:  022 07     lt           [r-3]          [r-2]          [381]
   500:  010 05     jnz          [381]           518
   503:  212 02     mul          [r-2]            -1           [r-1]
   507:  222 01     add          [r-3]          [r-1]          [r-3]
   511:  022 07     lt           [r-3]          [r-2]          [381]
   515:  010 06     jz           [381]           507
   518:  022 07     lt           [r-3]          [r-4]          [381]
   522:  010 05     jnz          [381]           540
   525:  212 02     mul          [r-4]            -1           [r-1]
   529:  222 01     add          [r-3]          [r-1]          [r-3]
   533:  022 07     lt           [r-3]          [r-4]          [381]
   537:  010 06     jz           [381]           529
   540:  221 02     mul             1           [r-3]          [r-7]
   544:  001 09     rel            -8
   546:  021 05     jnz             1           [r+0]
   549:  001 09     rel             4
   551:  012 02     mul          [r-2]            44           [566]
   555:  002 01     add          [r-3]          [566]          [566]
   559:  001 01     add           639           [566]          [566]
   563:  021 02     mul             1           [r-1]            [0]
   567:  002 04     out          [r-3]
   569:  002 04     out          [r-2]
   571:  002 04     out          [r-1]
   573:  001 09     rel            -4
   575:  021 06     jz              0           [r+0]
   578:  001 09     rel             3
   580:  012 02     mul          [r-1]            44           [594]
   584:  002 01     add          [r-2]          [594]          [594]
   588:  001 01     add           639           [594]          [594]
   592:  201 01     add             0             [0]          [r-2]
   596:  001 09     rel            -3
   598:  021 06     jz              0           [r+0]
   601:  001 09     rel             3
   603:  221 02     mul            24           [r-2]          [r+1]
   607:  222 01     add          [r+1]          [r-1]          [r+1]
   611:  211 01     add             0            541           [r+2]
   615:  211 01     add             0             17           [r+3]
   619:  211 02     mul             1           1056           [r+4]
   623:  211 02     mul           630              1           [r+0]
   627:  011 06     jz              0            456
   630:  212 01     add          [r+1]          1695           [r-2]
   634:  001 09     rel            -3
   636:  021 05     jnz             1           [r+0]
