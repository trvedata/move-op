set encoding utf8
set terminal postscript eps size 3,2.5 enhanced color
set output '| ps2pdf -dEPSCrop - crdt-optimised.pdf'
set multiplot layout 2,1
set key off
set style line 3 linewidth 2.5 linecolor rgb '#EE7733' pointsize 1.3 pointtype 5
set style line 4 linewidth 2.5 linecolor rgb '#EE3377' pointsize 1.3 pointtype 9

set size 1,0.6
set origin 0,0.4
set xrange [0:6200]
set yrange [0:300]
set ylabel 'Time [µs]'
set lmargin 10
set rmargin 3
set label 'Time to apply remote operation' at 1200,270
plot 'logs-crdt-optimised/summary.data' using ($2+$9+$16):($7+$14+$21)/3:($6+$13+$20)/3:($8+$15+$22)/3 with errorlines linestyle 3

set size 1,0.4
set xrange [0:6200]
set yrange [0:14]
set xlabel 'Move operations per second'
set ylabel 'Time [µs]'
set lmargin 10
set rmargin 3
set label 'Time to apply local operation' at 1200,11
plot 'logs-crdt-optimised/summary.data' using ($2+$9+$16):($4+$11+$18)/3:($3+$10+$17)/3:($5+$12+$19)/3 with errorlines linestyle 4
