"C:\Program Files\Wireshark\tshark.exe" -i Ethernet -l -f "udp port 53" -T fields -e dns.qry.name >> "C:\Users\....\dns.txt"
