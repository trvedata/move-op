set encoding utf8
set terminal postscript eps size 3,2.5 enhanced color
set output '| ps2pdf -dEPSCrop - crdt-generated.pdf'
set multiplot layout 2,1
set key off
set style line 1 linewidth 2.5 linecolor rgb '#0077BB' pointsize 1.3 pointtype 1
set style line 2 linewidth 2.5 linecolor rgb '#33BBEE' pointsize 1.3 pointtype 2

set size 1,0.6
set origin 0,0.4
set xrange [0:620]
set yrange [0:1900]
set ylabel 'Time [µs]'
set lmargin 10
set rmargin 3
set label 'Time to apply remote operation' at 120,1700
plot 'logs-crdt-generated/summary.data' using ($2+$9+$16):($7+$14+$21)/3:($6+$13+$20)/3:($8+$15+$22)/3 with errorlines linestyle 1

set size 1,0.4
set xrange [0:620]
set yrange [0:100]
set xlabel 'Move operations per second'
set ylabel 'Time [µs]'
set lmargin 10
set rmargin 3
set ytics 0,20
set label 'Time to apply local operation' at 120,80
plot 'logs-crdt-generated/summary.data' using ($2+$9+$16):($4+$11+$18)/3:($3+$10+$17)/3:($5+$12+$19)/3 with errorlines linestyle 2
