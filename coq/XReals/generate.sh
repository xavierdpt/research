#!/bin/bash
ls *.v | sed 's/^/Require Export /;s/v$//' 
