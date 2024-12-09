import os
import shutil
import subprocess
import time
import sys
import argparse
import re

boogie_proofgen_bin = 'boogieproof'
boogie_orig_bin = 'boogieorig'

# copies file to output directory such that the directory structure of the source destination is kept (relative to test_dir)
def store_file_in_output_dir(file_path, output_dir, test_dir):
    relpath = os.path.relpath(file_path, test_dir)
    print("Test dir: {}, File path: {}, Relative path: {}".format(test_dir, file_path, relpath))
    target_path = os.path.join(output_dir, relpath)

    os.makedirs(os.path.dirname(target_path), exist_ok=True)

    shutil.copyfile(file_path, target_path)

def adjust_and_filter(filename, output_dir, test_dir):
    n_supported_success = 0
    n_supported_error = 0
    n_empty_files = 0

    if(os.path.exists(output_dir)):
        print("Error: Output dir {} exists".format(output_dir))
        exit(1)

    os.mkdir(output_dir)
    output_filename = os.path.join(output_dir, "origin_list.txt")

    with open(output_filename, 'w') as output_file:
        with open(filename) as f:
            print("Starting next selection: Remove all attributes of files in first selection and check if they verify.")
            content = f.readlines()
            for line in content:
                boogie_file = line.rstrip()
                
                newStr = ""
                replaceFile = False
                include = True        
                with open(boogie_file) as f_other:
                    fileContent = f_other.read()
                    
                    #do not include files without any procedures
                    if (not ("procedure" in fileContent)):
                        n_empty_files += 1
                        include = False                      
                    else:
                        # remove attributes
                        if '{:' in fileContent:
                            newStr = re.sub('\{:.["a-zA-Z0-9_$#\.\+\(\) ]*\}','',fileContent)
                            replaceFile = True                            

                # store version without attributes
                if replaceFile and newStr != "":
                    with open(boogie_file, "w") as fout:
                        fout.write(newStr)
                
                if include:
                    # check whether Boogie can verify file with default options (we use the original Boogie version for this)            
                    output = subprocess.check_output([boogie_orig_bin,boogie_file])
                                
                    # space before 0, otherwise "10 errors" would succeed the test as well
                    if " 0 errors" in str(output) and (not ("inconclusive" in str(output))):    
                        n_supported_success += 1

                        print("Selected " + boogie_file) 

                        output_file.write(boogie_file+"\n")

                        store_file_in_output_dir(file_path=boogie_file, output_dir=output_dir, test_dir=test_dir)
                    else:
                        n_supported_error += 1
                        print("Failure:" + boogie_file)
                

        print("Found " + str(n_supported_success) + " potentially supported tests that are verified after removing all attributes.")
        # print("Found " + str(n_supported_error) + " tests that do not verify")
        # print("Found " + str(n_empty_files) + " tests without any procedures")

def main():
    parser = argparse.ArgumentParser()

    parser.add_argument(
        "-t", "--testdir",        
        help="Specify test directory containing the Boogie tests.",        
        required=True)

    parser.add_argument(
        "-o", "--outputdir",        
        help="Specify output directory containing the tests are verified by Boogie and that are (potentially) supported by proof generation.",        
        required=True)

    args = parser.parse_args()

    if(not(os.path.isdir(args.testdir))):
        print(args.testdir + " is not a directory.")
        exit(1)

    if(os.path.exists(args.outputdir)):
        print(args.outputdir + " already exists.")
        exit(1)
    
 
    # write all Boogie test file paths that are potentially supported by proof generation into a temporary file 
    filename = time.strftime("%Y%m%d-%H%M%S")+"_potentially_supported.log"
    with open(filename, 'w') as potentially_supported_file:
        print("Starting coarse-grained selection of tests")

        def file_potentially_supported_from_output(output):
            output_split = output.splitlines()
            return len(output_split) > 0 and output_split[0].startswith("Success:")

        n_candidate_files = 0

        for root, dirs, files in os.walk(args.testdir):
            for file in files:
                if file.endswith('.bpl'):
                    test_file_path = os.path.join(root, file)
                    n_candidate_files += 1

                    print(test_file_path)

                    # the option "/onlyCheckProofGenSupport" only performs a coarse-grained check whether
                    # proof generation supports a file and does not generate any proofs                  
                    process = subprocess.Popen([boogie_proofgen_bin, "/onlyCheckProofGenSupport",test_file_path], shell=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
                    output, error = process.communicate()
                    return_code = process.returncode
                    
                    if return_code == 0 and file_potentially_supported_from_output(output.decode('utf-8')):
                        print("success")
                        potentially_supported_file.write(test_file_path+"\n")
                    else:
                        print("error (return code: {}, error: {}, output: {})".format(return_code, error.decode('utf-8'), output.decode('utf-8')))

        print("Finished coarse-grained selection of tests")
    
    """ 
     From the identified files, select those tests that verify after removing attributes 
     (this has a side effect on the files --> attributes removed).
    """
    adjust_and_filter(filename, args.outputdir, args.testdir)

    # remove the temporary file
    os.remove(filename)


if __name__ == '__main__':
    main()