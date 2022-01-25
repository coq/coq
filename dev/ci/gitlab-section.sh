#!/bin/sh

case "$1" in
    start)
        printf '\e[0Ksection_start:%s:%s\r\e[0K%s\n' "$(date +%s)" "$2" "$3"
        ;;
    end)
        printf '\e[0Ksection_end:%s:%s\r\e[0K\n' "$(date +%s)" "$2"
        ;;
    *)
        >&2 echo "usage: $0 start|end section_name [header_content]"
        ;;
esac
