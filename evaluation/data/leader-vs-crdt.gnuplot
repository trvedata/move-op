set encoding utf8
set terminal postscript eps size 6,2.5 enhanced color
set output '| ps2pdf -dEPSCrop - leader-vs-crdt.pdf'
set key off

# Colour scheme from https://personal.sron.nl/~pault/data/colourschemes.pdf
set style line 1 linewidth 2.5 linecolor rgb '#0077BB' pointsize 1.3 pointtype 1
set style line 2 linewidth 2.5 linecolor rgb '#33BBEE' pointsize 1.3 pointtype 2
set style line 3 linewidth 2.5 linecolor rgb '#EE7733' pointsize 1.3 pointtype 5
set style line 4 linewidth 2.5 linecolor rgb '#EE3377' pointsize 1.3 pointtype 9
set style line 5 linewidth 2.5 linecolor rgb '#009988' pointsize 1.3 pointtype 6
set style line 6 linewidth 2.5 linecolor rgb '#CC3311' pointsize 1.3 pointtype 4

set logscale
set xlabel 'Move operations per second'
set ylabel 'Median response time per operation [µs]'
set label "CRDT remote operations\n(Isabelle-generated code)" at 30,3000 textcolor rgb '#0077BB'
set arrow from 80,900 to 100,300
set label "CRDT local operations\n(Isabelle-generated code)" at 300,250 textcolor rgb '#33BBEE'
set arrow from 290,190 to 200,50
set label "CRDT remote operations (optimised)" at 2100,13 textcolor rgb '#EE7733'
set arrow from 2000,13 to 1500,30
set label "CRDT local operations (optimised)" at 2100,5 textcolor rgb '#EE3377'
set arrow from 2000,5 to 1500,2
set label "Ireland to leader in California" at 60,50000 textcolor rgb '#009988'
set arrow from 57,50000 to 42,110000
set label "Singapore to leader in California" at 60,500000 textcolor rgb '#CC3311'
set arrow from 57,500000 to 42,220000
set label "Leader-based operations\n(Isabelle-generated code)" at 3000,50000
set arrow from 12000,70000 to 14000,500000
set label "Leader-based operations\n(optimised code)" at 4000,10000
set arrow from 17000,13000 to 20000,100000

plot 'logs-crdt-generated/summary.data' using ($2+$9+$16):($7+$14+$21)/3 with linespoints linestyle 1, \
    'logs-crdt-generated/summary.data' using ($2+$9+$16):($4+$11+$18)/3 with linespoints linestyle 2, \
    'logs-crdt-optimised/summary.data' using ($2+$9+$16):($7+$14+$21)/3 with linespoints linestyle 3, \
    'logs-crdt-optimised/summary.data' using ($2+$9+$16):($4+$11+$18)/3 with linespoints linestyle 4, \
    'logs-leader-generated/summary.data' using 2:5 with linespoints linestyle 5, \
    'logs-leader-generated/summary.data' using 2:9 with linespoints linestyle 6, \
    'logs-leader-optimised/summary.data' using 2:5 with linespoints linestyle 5, \
    'logs-leader-optimised/summary.data' using 2:9 with linespoints linestyle 6
