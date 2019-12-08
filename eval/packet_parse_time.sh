while read -d $'\0' file; do
    ../src/out/mqttPacketParser.out $file | grep time
done < <(find packets -mindepth 1 -maxdepth 1 -print0)
