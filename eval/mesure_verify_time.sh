#!/bin/bash
# make -C ../src mesure_verify_time
(time make -C ../src mesure_verify_time) 2>&1 | grep real | cut -b 5- | tr -d '\011'