#!/bin/bash

# Get the directory of the current script
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

# Change to the script directory
cd "$SCRIPT_DIR"

wget https://github.com/vprover/vampire/releases/download/v4.9casc2024/vampire
chmod +x ./vampire