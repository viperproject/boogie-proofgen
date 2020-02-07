﻿using System;
using System.Collections.Generic;

namespace ProofGeneration
{
    class Util
    {

        public static void Add<T, R>(T key, R val, IDictionary<T, IList<R>> dict)
        {
            IList<R> list;

            bool success = dict.TryGetValue(key, out list);
            if (!success)
            {
                list = new List<R>();
            }

            list.Add(val);
        }

        public static void AddEquation<T>(T lhs, T rhs, IList<Tuple<IList<T>, T>> equations)
        {
            equations.Add(new Tuple<IList<T>, T>(new List<T>() { lhs }, rhs));
        }

    }
}