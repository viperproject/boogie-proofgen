using System;
using System.Collections;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using Isabelle.Ast;
using Isabelle.IsaPrettyPrint;
using Microsoft.Boogie;
using ProofGeneration.Util;

namespace ProofGeneration
{
    public static class ProofGenerationOutput
    {
        private static string _mainDir;

        public static void CreateMainDirectory(string fileName, bool onlyUseFileName)
        {
            if (CommandLineOptions.Clo.DontStoreProofGenFiles)
                return;
            
            if (_mainDir != null)
                throw new ProofGenUnexpectedStateException("main directory already set");

            if (!onlyUseFileName)
                _mainDir = FreeDirName(Path.GetFileNameWithoutExtension(fileName) + "_proofs", false);
            else
                _mainDir = fileName;
            Directory.CreateDirectory(_mainDir);
        }
        
        public static void StoreTheoriesTopLevel(IEnumerable<Theory> theories)
        {
            if (CommandLineOptions.Clo.DontStoreProofGenFiles)
                return;
            
            if (_mainDir == null)
                throw new ProofGenUnexpectedStateException("main directory not yet set");

            foreach (var theory in theories) StoreTheory(_mainDir, theory);
        }
        
        /// <summary>
        /// Stores the provided theories into a new subdirectory with prefix <paramref name="preferredDirName"/>. The
        /// created subdirectory is located in the main proof generation directory used for the current run.
        /// Existing directories or files are not rewritten (i.e., a name that does not clash with any of the existing
        /// directories/files is picked)
        /// </summary>
        /// <param name="preferredDirName">Prefix of new directory.</param>
        /// <param name="theories">Theories to be stored.</param>
        /// <exception cref="ProofGenUnexpectedStateException">Thrown if main proof generation directory is not set.</exception>
        public static void StoreTheoriesInNewDirWithSession(string preferredDirName, IEnumerable<Theory> theories)
        {
            if (CommandLineOptions.Clo.DontStoreProofGenFiles)
                return;
            
            if (_mainDir == null)
                throw new ProofGenUnexpectedStateException("main directory not yet set");

            //create new directory
            var dirPath = Path.Join(_mainDir, FreeDirName(preferredDirName + "_proofs", true));
            Directory.CreateDirectory(dirPath);

            foreach (var theory in theories) StoreTheory(dirPath, theory);

            //StoreSessionRoot(dirPath, theories);
        }

        private static string NameWithId(string prefix, int id)
        {
            if (id == 1)
                return prefix;
            return prefix + "_" + id;
        }

        private static string FreeDirName(string preferredName, bool insideMainDir)
        {
            Func<string, string> dirPath = 
                dirName => (insideMainDir && _mainDir != null) ? Path.Combine(_mainDir, dirName) : dirName;
            
            var i = 1;
            while (Directory.Exists(dirPath(NameWithId(preferredName, i)))) i++;

            return NameWithId(preferredName, i);
        }

        private static void StoreTheory(string dirName, Theory theory)
        {
            var path = Path.Combine(dirName, theory.TheoryName + ".thy");
            var sw = new StreamWriter(path);
            var theoryString = IsaPrettyPrinter.PrintTheory(theory);

            sw.WriteLine(theoryString);
            sw.Close();
        }

        private static string ExtractTheoryName(string filename)
        {
            var theoryFile = Path.GetFileName(filename);
            return theoryFile.Remove(theoryFile.Length - 4, 4);
        }

        private static string CombineLinux(string dir, string file)
        {
            return dir + "/" + file;
        }

        private static string SessionName(string preferredName)
        {
            //hyphens are not allowed in session names
            return preferredName.Replace('-', '_').Replace('\'', 'A');
        }
        
        public static void FinishStoring()
        {
            if (CommandLineOptions.Clo.DontStoreProofGenFiles)
                return;
            
            if (_mainDir == null)
                throw new ProofGenUnexpectedStateException("main directory not yet set");

            using var sw = new StreamWriter(Path.Combine(_mainDir, "ROOT"));

            var sessionName = new IsaUniqueNamer().GetName(Path.GetFileName(_mainDir));
              
            sw.WriteLine("session " + SessionName(sessionName) + " = " + "Boogie_Lang + ");
            
            var subDirs = Directory.EnumerateDirectories(_mainDir).ToList();
            if (subDirs.Any())
                sw.WriteLine("directories " + String.Join(" ", subDirs.Select(Path.GetFileName)));
    
            sw.WriteLine("theories");
            sw.WriteLine(string.Join(Environment.NewLine,
                Directory.EnumerateFiles(_mainDir).Where(f => f.EndsWith(".thy")).Select(ExtractTheoryName)));
                
            foreach (var subDir in subDirs)
            {
                var subDirName = Path.GetFileName(subDir);
                var theoryFiles = Directory.EnumerateFiles(subDir)
                    .Where(f => f.EndsWith(".thy")).Select(ExtractTheoryName);
                sw.WriteLine(string.Join(Environment.NewLine, theoryFiles.Select(thy => "\""+ CombineLinux(subDirName, thy) + "\"")));
            }
        }
    }
}