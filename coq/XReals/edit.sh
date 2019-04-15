#!/bin/bash
coqide -R . Top "$1.v" 2>/dev/null &
