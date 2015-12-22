#!/bin/bash

./pscala -o - "$1" | vim -c "set ft=gas" -
