using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Diagnostics;
using System.IO;
using System.Threading;

namespace ContingentPlanning
{
    class SDRPlanner
    {
        public static bool SDR_OBS { set; get; }

        public enum Planners { FF, FFsa, FFha, MIPS, MetricFF, LPG, FD }
        public enum Translations { SDR, MPSRTagPartitions, MPSRTags, BestCase }

        private static Dictionary<Thread, Process> FFProcesses = new Dictionary<Thread, Process>();

        public static Planners Planner = Planners.FF;
        //public static Translations Translation = Translations.MPSRTags;
        public static Translations Translation = Translations.BestCase;


        public static bool OptimizeMemoryConsumption = true;
        public static bool ComputeCompletePlanTree = true;
        public static TimeSpan PlannerTimeout = new TimeSpan(0, 20, 0);
        public static bool WriteAllKVariations = false;
        public static bool ConsiderStateNegations = false;
        public static bool SplitConditionalEffects = false;
        public static bool RemoveAllKnowledge = true;
        public static bool ForceTagObservations = false;
        public static bool EnforceCNF = false;
        public static bool UseFilesForPlanners = false;
        public static bool UseDomainSpecificHeuristics = false;

        public static bool AddAllKnownToGiven { get; set; }
        public static bool AddTagRefutationToGoal { get; set; }

        public static List<string> SimulationStartState { get; set; }
        public static string GivenPlanFile = null;

        public static int TagsCount { get; set; }

        //TODO - to remove
        public int amount_of_offline_pruned_states;

        
    }


}
