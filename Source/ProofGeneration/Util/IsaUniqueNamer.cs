using System.Collections.Generic;
using System.Linq;
using System.Text.RegularExpressions;
using Microsoft.Boogie.VCExprAST;

namespace ProofGeneration.Util
{
    public class IsaUniqueNamer
    {
        private readonly List<char> illegalChars;

        private readonly HashSet<string> reservedNames;

        private readonly string spacer;
        private readonly UniqueNamer uniqueNamer;

        public IsaUniqueNamer(string spacer)
        {
            this.spacer = spacer;
            uniqueNamer = new KeepOriginalNamer
            {
                Spacer = spacer
            };
            reservedNames = new HashSet<string>();
            reservedNames.Add("A"); //value to abstract value map
            reservedNames.Add("abs");

            illegalChars = new List<char>();
            illegalChars.Add('@');
            illegalChars.Add('.');
            illegalChars.Add('$');
            illegalChars.Add('?');
        }

        public IsaUniqueNamer() : this("AA")
        {
        }

        /// <summary>
        /// Same as invoking <see cref="GetName(object, string)"/> with input string is the same for both arguments. 
        /// </summary>
        public string GetName(string preferredName)
        {
            return GetName(preferredName, preferredName);
        }
        
        public string RemoveApostropheInFunc(string preferredName)
        {
          return RemoveApostropheInFunc(preferredName, preferredName);
        }

        /// <summary>
        /// Returns a unique, legal Isabelle name resembling <paramref name="preferredName"/>.
        /// <paramref name="obj"/> functions as a key. This means that any call to this method where the key is the same
        /// must return the same output. Uniqueness is w.r.t. all names that have been returned by this method.
        /// </summary>
        public string GetName(object obj, string preferredName)
        {
            var preferredNameMod = preferredName;
            foreach (var illegalChar in illegalChars) preferredNameMod = preferredNameMod.Replace(illegalChar, '_');

            /* TODO: might need to replace numbers in some cases for ROOT file
            if (preferredNameMod.Contains('0')) preferredNameMod = preferredNameMod.Replace('0', 'a'); 
            if (preferredNameMod.Contains('1')) preferredNameMod = preferredNameMod.Replace('1', 'b'); 
            if (preferredNameMod.Contains('2')) preferredNameMod = preferredNameMod.Replace('2', 'c'); 
            if (preferredNameMod.Contains('3')) preferredNameMod = preferredNameMod.Replace('3', 'd'); 
            if (preferredNameMod.Contains('4')) preferredNameMod = preferredNameMod.Replace('4', 'e'); 
            if (preferredNameMod.Contains('5')) preferredNameMod = preferredNameMod.Replace('5', 'f'); 
            if (preferredNameMod.Contains('6')) preferredNameMod = preferredNameMod.Replace('6', 'g'); 
            if (preferredNameMod.Contains('7')) preferredNameMod = preferredNameMod.Replace('7', 'h'); 
            if (preferredNameMod.Contains('8')) preferredNameMod = preferredNameMod.Replace('8', 'i'); 
            if (preferredNameMod.Contains('9')) preferredNameMod = preferredNameMod.Replace('9', 'j');
            */

            if (reservedNames.Contains(preferredNameMod)) preferredNameMod = preferredNameMod + "ZZ";
            if (preferredName.Length > 0 && preferredName.Last() == '_') preferredNameMod = preferredNameMod + "n";

            return uniqueNamer.GetName(obj, GetValidIsaString(preferredNameMod));
        }

        public string RemoveApostrophe(object obj, string preferredName)
        {
          var preferredNameMod = preferredName;
          if (preferredNameMod.Contains("\'" + "\'" + "\'"))
          {
            preferredNameMod = preferredNameMod.Replace("\'" + "\'" + "\'", "AA" + "\'" + "\'");
          }

          return uniqueNamer.GetName(obj, preferredNameMod);
        }
        
        public string RemoveApostropheInFunc(object obj, string preferredName)
        {
          var preferredNameMod = preferredName;
          if (preferredNameMod.Contains("\'"))
          {
            preferredNameMod = preferredNameMod.Replace("\'", "AA");
          }

          return uniqueNamer.GetName(obj, preferredNameMod);
        }

        public string GetLocalName(object obj, string preferredName)
        {
            return uniqueNamer.GetLocalName(obj, GetValidIsaString(preferredName));
        }

        public void PushScope()
        {
            uniqueNamer.PushScope();
        }

        public void PopScope()
        {
            uniqueNamer.PopScope();
        }

        private string GetValidIsaString(string s)
        {
            var firstChar = new Regex("^[A-Za-z]");

            var sMod = s;

            if (!firstChar.IsMatch(s))
                sMod = "isa" + spacer + s;

            var illegalCharacters = new Regex("[@#^*!&]");

            return illegalCharacters.Replace(sMod, spacer);
        }
    }
}