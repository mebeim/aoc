     0:  011 02     mul      34463338       34463338            [63]
     4:  010 07     lt            [63]      34463338            [63]
     8:  010 05     jnz           [63]            53
    11:  011 02     mul             3              1          [1000]
    15:  001 09     rel           988
    17:  002 09     rel         [r+12]
    19:  000 09     rel         [1000]
    21:  002 09     rel          [r+6]
    23:  002 09     rel          [r+3]
    25:  002 03     in           [r+0]
    27:  010 08     eq          [1000]             1            [63]
    31:  010 05     jnz           [63]            65
    34:  010 08     eq          [1000]             2            [63]
    38:  010 05     jnz           [63]           902
    41:  010 08     eq          [1000]             0            [63]
    45:  010 05     jnz           [63]            58
    48:  000 04     out           [25]
    50:  001 04     out             0
    52:  000 99     hlt
    53:  000 04     out            [0]
    55:  001 04     out             0
    57:  000 99     hlt
    58:  000 04     out           [17]
    60:  001 04     out             0
    62:  000 99     hlt
    63:  000 00     (bad)
    64:  000 00     (bad)
    65:  011 01     add           309              0          [1024]
    69:  011 01     add             0             24          [1002]
    73:  011 02     mul           388              1          [1029]
    77:  011 02     mul             1             21          [1019]
    81:  011 01     add             0             33          [1015]
    85:  011 02     mul             1            304          [1025]
    89:  011 01     add           344              0          [1027]
    93:  011 01     add            25              0          [1003]
    97:  011 02     mul             1              1          [1021]
   101:  011 01     add            29              0          [1012]
   105:  011 01     add             0             23          [1005]
   109:  011 02     mul             1             32          [1007]
   113:  011 02     mul            38              1          [1000]
   117:  011 01     add            30              0          [1016]
   121:  011 02     mul             1            347          [1026]
   125:  011 01     add             0             26          [1010]
   129:  011 01     add             0             39          [1004]
   133:  011 02     mul             1             36          [1011]
   137:  011 01     add             0            393          [1028]
   141:  011 01     add             0             37          [1013]
   145:  011 01     add             0             35          [1008]
   149:  011 01     add            34              0          [1001]
   153:  011 01     add             0            495          [1022]
   157:  011 02     mul             1             28          [1018]
   161:  011 01     add             0              0          [1020]
   165:  011 02     mul             1             22          [1006]
   169:  011 01     add           488              0          [1023]
   173:  011 02     mul            31              1          [1009]
   177:  011 02     mul             1             20          [1017]
   181:  011 01     add             0             27          [1014]
   185:  001 09     rel            10
   187:  211 02     mul            40              1           [r+4]
   191:  010 08     eq          [1014]            37            [63]
   195:  010 05     jnz           [63]           205
   198:  010 01     add           [64]             1            [64]
   202:  011 06     jz              0            207
   205:  000 04     out          [187]
   207:  010 02     mul           [64]             2            [64]
   211:  001 09     rel           -18
   213:  012 07     lt           [r+8]            37            [63]
   217:  010 05     jnz           [63]           227
   220:  010 01     add           [64]             1            [64]
   224:  011 06     jz              0            229
   227:  000 04     out          [213]
   229:  010 02     mul           [64]             2            [64]
   233:  001 09     rel            17
   235:  012 07     lt           [r-7]            25            [63]
   239:  010 05     jnz           [63]           247
   242:  000 04     out          [235]
   244:  011 06     jz              0            251
   247:  010 01     add           [64]             1            [64]
   251:  010 02     mul           [64]             2            [64]
   255:  001 09     rel            -8
   257:  012 02     mul          [r+6]             1            [63]
   261:  010 08     eq            [63]            29            [63]
   265:  010 05     jnz           [63]           275
   268:  010 01     add           [64]             1            [64]
   272:  011 06     jz              0            277
   275:  000 04     out          [257]
   277:  010 02     mul           [64]             2            [64]
   281:  001 09     rel            25
   283:  012 05     jnz          [r-6]           293
   286:  010 01     add           [64]             1            [64]
   290:  011 05     jnz             1            295
   293:  000 04     out          [283]
   295:  010 02     mul           [64]             2            [64]
   299:  001 09     rel            -4
   301:  021 05     jnz             1           [r+2]
   304:  000 04     out          [301]
   306:  011 06     jz              0            313
   309:  010 01     add           [64]             1            [64]
   313:  010 02     mul           [64]             2            [64]
   317:  001 09     rel            -9
   319:  012 08     eq           [r-4]            31            [63]
   323:  010 05     jnz           [63]           335
   326:  000 04     out          [319]
   328:  010 01     add           [64]             1            [64]
   332:  011 05     jnz             1            335
   335:  010 02     mul           [64]             2            [64]
   339:  001 09     rel            16
   341:  021 06     jz              0           [r-2]
   344:  011 06     jz              0            353
   347:  000 04     out          [341]
   349:  010 01     add           [64]             1            [64]
   353:  010 02     mul           [64]             2            [64]
   357:  001 09     rel           -13
   359:  021 02     mul             1           [r-8]           [63]
   363:  010 08     eq            [63]            38            [63]
   367:  010 05     jnz           [63]           373
   370:  011 05     jnz             1            379
   373:  000 04     out          [359]
   375:  010 01     add           [64]             1            [64]
   379:  010 02     mul           [64]             2            [64]
   383:  001 09     rel             9
   385:  021 06     jz              0           [r+3]
   388:  000 04     out          [385]
   390:  011 05     jnz             1            397
   393:  010 01     add           [64]             1            [64]
   397:  010 02     mul           [64]             2            [64]
   401:  001 09     rel           -11
   403:  211 07     lt             41             42           [r+0]
   407:  010 05     jnz         [1014]           415
   410:  000 04     out          [403]
   412:  011 06     jz              0            419
   415:  010 01     add           [64]             1            [64]
   419:  010 02     mul           [64]             2            [64]
   423:  001 09     rel            14
   425:  012 06     jz           [r-7]           431
   428:  011 06     jz              0            437
   431:  000 04     out          [425]
   433:  010 01     add           [64]             1            [64]
   437:  010 02     mul           [64]             2            [64]
   441:  001 09     rel           -23
   443:  021 07     lt             37           [r-5]           [63]
   447:  010 05     jnz           [63]           455
   450:  000 04     out          [443]
   452:  011 05     jnz             1            459
   455:  010 01     add           [64]             1            [64]
   459:  010 02     mul           [64]             2            [64]
   463:  001 09     rel            10
   465:  211 07     lt             42             41           [r-2]
   469:  010 05     jnz         [1013]           475
   472:  011 05     jnz             1            481
   475:  000 04     out          [465]
   477:  010 01     add           [64]             1            [64]
   481:  010 02     mul           [64]             2            [64]
   485:  021 05     jnz             1           [r+8]
   488:  010 01     add           [64]             1            [64]
   492:  011 06     jz              0            497
   495:  000 04     out          [485]
   497:  010 02     mul           [64]             2            [64]
   501:  001 09     rel            -6
   503:  211 08     eq             43             41           [r+8]
   507:  010 05     jnz         [1017]           517
   510:  010 01     add           [64]             1            [64]
   514:  011 06     jz              0            519
   517:  000 04     out          [503]
   519:  010 02     mul           [64]             2            [64]
   523:  001 09     rel             5
   525:  021 01     add             0           [r-9]           [63]
   529:  010 08     eq            [63]            23            [63]
   533:  010 05     jnz           [63]           541
   536:  000 04     out          [525]
   538:  011 06     jz              0            545
   541:  010 01     add           [64]             1            [64]
   545:  010 02     mul           [64]             2            [64]
   549:  001 09     rel           -13
   551:  012 01     add          [r+5]             0            [63]
   555:  010 08     eq            [63]            20            [63]
   559:  010 05     jnz           [63]           565
   562:  011 05     jnz             1            571
   565:  000 04     out          [551]
   567:  010 01     add           [64]             1            [64]
   571:  010 02     mul           [64]             2            [64]
   575:  001 09     rel            16
   577:  012 05     jnz          [r+4]           589
   580:  000 04     out          [577]
   582:  010 01     add           [64]             1            [64]
   586:  011 06     jz              0            589
   589:  010 02     mul           [64]             2            [64]
   593:  001 09     rel           -16
   595:  012 02     mul          [r+4]             1            [63]
   599:  010 08     eq            [63]            23            [63]
   603:  010 05     jnz           [63]           615
   606:  000 04     out          [595]
   608:  010 01     add           [64]             1            [64]
   612:  011 06     jz              0            615
   615:  010 02     mul           [64]             2            [64]
   619:  001 09     rel             1
   621:  021 01     add             0           [r+6]           [63]
   625:  010 08     eq            [63]            33            [63]
   629:  010 05     jnz           [63]           639
   632:  010 01     add           [64]             1            [64]
   636:  011 05     jnz             1            641
   639:  000 04     out          [621]
   641:  010 02     mul           [64]             2            [64]
   645:  001 09     rel             8
   647:  211 01     add            44              0           [r+8]
   651:  010 08     eq          [1018]            44            [63]
   655:  010 05     jnz           [63]           667
   658:  000 04     out          [647]
   660:  010 01     add           [64]             1            [64]
   664:  011 05     jnz             1            667
   667:  010 02     mul           [64]             2            [64]
   671:  001 09     rel            -7
   673:  012 01     add          [r+1]             0            [63]
   677:  010 08     eq            [63]            39            [63]
   681:  010 05     jnz           [63]           689
   684:  000 04     out          [673]
   686:  011 06     jz              0            693
   689:  010 01     add           [64]             1            [64]
   693:  010 02     mul           [64]             2            [64]
   697:  001 09     rel             7
   699:  021 02     mul             1           [r-8]           [63]
   703:  010 08     eq            [63]            24            [63]
   707:  010 05     jnz           [63]           715
   710:  000 04     out          [699]
   712:  011 05     jnz             1            719
   715:  010 01     add           [64]             1            [64]
   719:  010 02     mul           [64]             2            [64]
   723:  001 09     rel             5
   725:  021 08     eq             34           [r-7]           [63]
   729:  010 05     jnz           [63]           739
   732:  010 01     add           [64]             1            [64]
   736:  011 05     jnz             1            741
   739:  000 04     out          [725]
   741:  010 02     mul           [64]             2            [64]
   745:  001 09     rel           -22
   747:  021 08     eq             25          [r+10]           [63]
   751:  010 05     jnz           [63]           763
   754:  000 04     out          [747]
   756:  010 01     add           [64]             1            [64]
   760:  011 06     jz              0            763
   763:  010 02     mul           [64]             2            [64]
   767:  001 09     rel            31
   769:  012 06     jz           [r-4]           781
   772:  000 04     out          [769]
   774:  010 01     add           [64]             1            [64]
   778:  011 05     jnz             1            781
   781:  010 02     mul           [64]             2            [64]
   785:  001 09     rel           -10
   787:  211 01     add            45              0           [r+5]
   791:  010 08     eq          [1019]            47            [63]
   795:  010 05     jnz           [63]           805
   798:  010 01     add           [64]             1            [64]
   802:  011 05     jnz             1            807
   805:  000 04     out          [787]
   807:  010 02     mul           [64]             2            [64]
   811:  001 09     rel             2
   813:  211 08     eq             46             46           [r-3]
   817:  010 05     jnz         [1013]           825
   820:  000 04     out          [813]
   822:  011 06     jz              0            829
   825:  010 01     add           [64]             1            [64]
   829:  010 02     mul           [64]             2            [64]
   833:  001 09     rel           -22
   835:  021 07     lt             40          [r+10]           [63]
   839:  010 05     jnz           [63]           845
   842:  011 05     jnz             1            851
   845:  000 04     out          [835]
   847:  010 01     add           [64]             1            [64]
   851:  010 02     mul           [64]             2            [64]
   855:  001 09     rel            17
   857:  012 08     eq           [r-7]            36            [63]
   861:  010 05     jnz           [63]           871
   864:  010 01     add           [64]             1            [64]
   868:  011 05     jnz             1            873
   871:  000 04     out          [857]
   873:  010 02     mul           [64]             2            [64]
   877:  001 09     rel            16
   879:  211 02     mul            47              1           [r-9]
   883:  010 08     eq          [1018]            47            [63]
   887:  010 05     jnz           [63]           899
   890:  000 04     out          [879]
   892:  010 01     add           [64]             1            [64]
   896:  011 06     jz              0            899
   899:  000 04     out           [64]
   901:  000 99     hlt
   902:  211 02     mul             1             27           [r+1]
   906:  211 01     add             0            913           [r+0]
   910:  011 05     jnz             1            920
   913:  212 01     add          [r+1]         39657           [r+1]
   917:  002 04     out          [r+1]
   919:  000 99     hlt
   920:  001 09     rel             3
   922:  012 07     lt           [r-2]             3            [63]
   926:  010 05     jnz           [63]           962
   929:  212 01     add          [r-2]            -1           [r+1]
   933:  211 02     mul             1            940           [r+0]
   937:  011 05     jnz             1            920
   940:  212 01     add          [r+1]             0           [r-1]
   944:  212 01     add          [r-2]            -3           [r+1]
   948:  211 01     add           955              0           [r+0]
   952:  011 05     jnz             1            920
   955:  222 01     add          [r+1]          [r-1]          [r-2]
   959:  011 06     jz              0            966
   962:  212 02     mul          [r-2]             1           [r-2]
   966:  001 09     rel            -3
   968:  021 05     jnz             1           [r+0]
