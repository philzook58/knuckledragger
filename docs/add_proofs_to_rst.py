#!/usr/bin/env python3
"""
Post-process generated RST files to add Proof objects.
"""

import os
import sys
import importlib
import kdrag as kd

def process_rst_file(rst_path, module_name):
    """Add Proof objects to an RST file."""
    try:
        # Import the module
        module = importlib.import_module(module_name)
        
        # Find Proof objects
        proof_objects = []
        for name in sorted(dir(module)):
            if not name.startswith('_'):
                obj = getattr(module, name)
                if isinstance(obj, kd.Proof):
                    proof_objects.append(name)
        
        if not proof_objects:
            return False
        
        # Read the existing RST content
        with open(rst_path, 'r') as f:
            content = f.read()
        
        # Check if we already added Proof objects - remove old section first
        if '.. rubric:: Proof Objects' in content or 'Proof Objects\n---' in content:
            # Remove the old Proof Objects section
            markers = ['.. rubric:: Proof Objects', 'Proof Objects\n-------------', 'Proof Objects\n---']
            for marker in markers:
                if marker in content:
                    start = content.find(marker)
                    end = content.find('.. literalinclude::', start)
                    if end == -1:
                        end = len(content)
                    content = content[:start] + content[end:]
                    break
        
        # Find the position to insert (before literalinclude)
        lit_pos = content.find('.. literalinclude::')
        if lit_pos == -1:
            # Insert at the end
            insert_pos = len(content)
        else:
            insert_pos = lit_pos
        
        # Create the Proof objects section as a proper RST section at the same level as the module
        proof_section = 'Proof Objects\n-------------\n\n'
        proof_section += 'The following theorem proofs are available in this module:\n\n'
        for name in proof_objects:
            # Get the actual proof object to show its theorem
            obj = getattr(module, name)
            theorem_str = repr(obj.thm)
            proof_section += f'.. py:data:: {name}\n'
            proof_section += f'   :module: {module_name}\n'
            proof_section += f'   :type: kdrag.Proof\n'
            proof_section += f'   :value: {theorem_str}\n\n'
        
        # Add an extra newline before literalinclude
        proof_section += '\n'
        
        # Insert the section
        new_content = content[:insert_pos] + proof_section + content[insert_pos:]
        
        # Write back
        with open(rst_path, 'w') as f:
            f.write(new_content)
        
        return True
        
    except Exception as e:
        print(f"Error processing {module_name}: {e}", file=sys.stderr)
        return False

def main():
    """Process all RST files in _autosummary."""
    autosummary_dir = '_autosummary'
    if not os.path.exists(autosummary_dir):
        print(f"Directory {autosummary_dir} not found")
        return
    
    processed = 0
    # Only process theory modules that are likely to have Proof objects
    theory_modules = [
        'kdrag.theories.nat',
        'kdrag.theories.int',
        'kdrag.theories.list',
        'kdrag.theories.seq',
        'kdrag.theories.logic.zf',
        'kdrag.theories.bitvec',
        'kdrag.theories.set',
        'kdrag.theories.algebra.group',
        'kdrag.theories.algebra.vector',
    ]
    
    for module_name in theory_modules:
        rst_filename = module_name + '.rst'
        rst_path = os.path.join(autosummary_dir, rst_filename)
        
        if os.path.exists(rst_path):
            if process_rst_file(rst_path, module_name):
                processed += 1
                print(f"Processed: {module_name}")
    
    print(f"\nProcessed {processed} files")

if __name__ == '__main__':
    main()
