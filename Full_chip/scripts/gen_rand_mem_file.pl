#!/usr/bin/perl -w
# -------------------------------------------------------------
# PROJECT    : ECE 510 PRESILICON VALIDATION FINAL PROJECT
# DESCRIPTION: SCRIPT TO GENERATE RANDOM MEM FILES TO BE LOADED 
#              AS STIMULUS IN FULL CHIP TESTBENCH 
# AUTHOR     : ROHIT KULKARNI
# DATE       : JUNE 9, 2015
# -------------------------------------------------------------


use strict;
use warnings;

# Auto flush buffer
$| = 1; 

# Rand seed
srand 2;

# Globals
my $out_file_name = "test.mem";
my $rnd_range = 4095;

# Subroutines
sub open_mem;
sub gen_rand_mem_file;
sub close_mem;

# Open file in write mode
sub open_mem
{
    open (MEM_FILE, ">$out_file_name") or die "$! error trying to open mem file";
}    


# Generate random mem file here
sub gen_rand_mem_file
{
    my $i;
    my $rand_instr;

    print MEM_FILE '@080';
    print MEM_FILE "\nec0";

        
    for($i = 0; $i < 4093; $i++)
    {
	$rand_instr = int(rand($rnd_range));
	printf(MEM_FILE "\n%x", $rand_instr);
    }

    print MEM_FILE "\nf02";
    print MEM_FILE "\na80";
    


    print "\nMem File generated successfully.\n";
}


# Close mem
sub close_mem
{
    close MEM_FILE; 
}



# Main
&open_mem;
&gen_rand_mem_file;
&close_mem;    
