#!/bin/bash
# System monitor for tmux dashboard

while true; do
    clear
    echo "=== System Monitor ==="
    echo ""
    
    # CPU usage
    cpu=$(top -bn1 | grep "Cpu(s)" | awk '{print $2}' | cut -d'%' -f1)
    printf "CPU:  "
    awk -v val="$cpu" 'BEGIN { 
        filled = int(val/10); 
        for(i=1;i<=10;i++) printf (i<=filled) ? "█" : "░" 
    }'
    printf " %.0f%%\n" "$cpu"
    
    # Memory usage
    mem_info=$(free -m | awk 'NR==2{printf "%.0f %.0f %.0f", $3, $2, ($3/$2)*100}')
    mem_used=$(echo $mem_info | cut -d' ' -f1)
    mem_total=$(echo $mem_info | cut -d' ' -f2)
    mem_percent=$(echo $mem_info | cut -d' ' -f3)
    
    printf "MEM:  "
    awk -v val="$mem_percent" 'BEGIN { 
        filled = int(val/10); 
        for(i=1;i<=10;i++) printf (i<=filled) ? "█" : "░" 
    }'
    printf " %d%% (%sM/%sM)\n" "$mem_percent" "$mem_used" "$mem_total"
    
    # Disk usage
    disk_info=$(df -h / | awk 'NR==2{print $5 " " $3 " " $2}' | sed 's/%//')
    disk_percent=$(echo $disk_info | cut -d' ' -f1)
    disk_used=$(echo $disk_info | cut -d' ' -f2)
    disk_total=$(echo $disk_info | cut -d' ' -f3)
    
    printf "DISK: "
    awk -v val="$disk_percent" 'BEGIN { 
        filled = int(val/10); 
        for(i=1;i<=10;i++) printf (i<=filled) ? "█" : "░" 
    }'
    printf " %d%% (%s/%s)\n" "$disk_percent" "$disk_used" "$disk_total"
    
    echo ""
    echo "PROC: $(pgrep -c node) node, $(pgrep -c java) java"
    echo "LOAD: $(uptime | awk -F'load average:' '{print $2}')"
    
    sleep 2
done
