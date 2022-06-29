using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.IO;
using System.Diagnostics;

namespace PDDL
{
    public class Domain
    {
        public string Name { get; protected set; }
        public List<string> Types { get; private set; }
        public List<Action> Actions { get; protected set; }
        public List<Constant> Constants { get; protected set; }
        public List<Predicate> Predicates { get; protected set; }
        public List<string> Functions { get; protected set; }
        public List<string> m_lAlwaysKnown { get; protected set; }
        private List<string> m_lAlwaysConstant;
        private List<string> m_lObservable;
        public string Path { get; private set; }

        public bool m_bUseOptions = true;
        public bool m_bReplaceNonDeterministicEffectsWithOptions = true;
        public bool UseCosts { get; private set; }

        public const string OPTION = "OPTION_TYPE";
        public const string OPTION_PREDICATE = "option";
        public const string VALUE = "VALUE_TYPE";
        public const string VALUE_PARAMETER = "?V_PARAM";
        public const string TAG = "TAG_TYPE";
        public const string TAG_PARAMETER = "?TAG_PARAM";
        public const string TRUE_VALUE = "V_TRUE";
        public const string FALSE_VALUE = "V_FALSE";
        public const string TRUE_PREDICATE = "P_TRUE";
        public const string FALSE_PREDICATE = "P_FALSE";

        public const int TIME_STEPS = 0;
        public const int MAX_OPTIONS = 3;


        public bool RemoveConflictingConditionalEffects = false;
        private Dictionary<Predicate, Predicate> m_dAuxilaryPredicates;


        public Domain(string sName, string sPath)
        {
            UseCosts = true;
            Name = sName;
            Path = sPath;
            Actions = new List<Action>();
            Constants = new List<Constant>();
            Predicates = new List<Predicate>();
            Types = new List<string>();
            m_lAlwaysKnown = new List<string>();
            m_lAlwaysKnown.Add("increase");
            m_lAlwaysKnown.Add("decrease");
            m_lAlwaysKnown.Add("=");
            m_lAlwaysConstant = new List<string>();
            m_lObservable = new List<string>();
            m_dAuxilaryPredicates = new Dictionary<Predicate, Predicate>();
            Functions = new List<string>();
        }

        public void AddAction(Action a)
        {
            Actions.Add(a);
            if (a.Effects != null)
            {
                HashSet<Predicate> lConditionalEffects = new HashSet<Predicate>();
                HashSet<Predicate> lNonConditionalEffects = new HashSet<Predicate>();

                a.Effects.GetAllEffectPredicates(lConditionalEffects, lNonConditionalEffects);

                foreach (Predicate p in lConditionalEffects)
                {
                    m_lAlwaysKnown.Remove(p.Name);
                    m_lAlwaysConstant.Remove(p.Name);
                }
                foreach (Predicate p in lNonConditionalEffects)
                {
                    m_lAlwaysConstant.Remove(p.Name);
                }
                List<Predicate> lNonDetEffects = a.GetNonDeterministicEffects();
                if (lNonDetEffects != null)
                {
                    foreach (Predicate p in lNonDetEffects)
                    {
                        m_lAlwaysKnown.Remove(p.Name);
                    }
                }

            }
            else if (a.Effects is PredicateFormula)
            {
                Predicate p = ((PredicateFormula)a.Effects).Predicate;
                m_lAlwaysConstant.Remove(p.Name);
            }
            if (a.Observe != null)
            {
                foreach(Predicate p in a.Observe.GetAllPredicates())
                    m_lObservable.Add(p.Name);
            }
        }
        public void AddConstant(Constant c)
        {
            Constants.Add(c);
        }
        public void AddPredicate(Predicate p)
        {
            Predicates.Add(p);
            m_lAlwaysKnown.Add(p.Name);
            m_lAlwaysConstant.Add(p.Name);
        }
        public override string ToString()
        {
            string s = "(domain " + Name + "\n";
            s += "(constants " + Parser.ListToString(Constants) + ")\n";
            s += "(predicates " + Parser.ListToString(Predicates) + ")\n";
            s += "(actions " + Parser.ListToString(Actions) + ")\n";
            s += ")";
            return s;
        }

        //not really checking everything - need to check compatible parameters, constants and so forth
        public bool ContainsPredicate(string sName)
        {
            foreach (Predicate p in Predicates)
                if (p.Name == sName)
                    return true;
            return false;
        }

        public Constant GetConstant(string sName)
        {
            foreach(Constant c in Constants)
                if(c.Name == sName)
                    return c;
            return null;
        }

        public void WriteKnowledgeDomain(string sFileName, Problem p)
        {
            StreamWriter sw = new StreamWriter(sFileName);
            sw.WriteLine("(define (domain K" + Name + ")");
            sw.WriteLine("(:requirements :strips :typing)");
            WriteTypes(sw, false);
            WriteConstants(sw);
            sw.WriteLine();
            WriteKnowledgePredicates(sw);
            sw.WriteLine();
            WriteKnowledgeActions(sw);
            p.WriteReasoningActions(sw);
            sw.WriteLine(")");
            sw.Close();
        }

        
        //know whether - no s_0
        public void WriteTaggedDomainNoState(string sFileName, Dictionary<string, List<Predicate>> dTags, Problem pCurrent)
        {
            if (HasNonDeterministicActions() && m_bUseOptions)
            {
                Domain dDeterministic = RemoveNonDeterministicEffects();
                dDeterministic.WriteTaggedDomainNoState(sFileName, dTags, pCurrent); 
                return;
            }


            StreamWriter sw = new StreamWriter(sFileName);
            sw.WriteLine("(define (domain K" + Name + ")");
            
            
            sw.WriteLine("(:requirements :strips :typing)");
            
            WriteFunctions(sw);
            WriteTypes(sw, true);
            WriteConstants(sw, dTags);
            sw.WriteLine();
            if (SDRPlanner.SplitConditionalEffects)
            {
                List<Predicate> lAdditionalPredicates = new List<Predicate>();
                List<Action> lAllActions = GetKnowledgeActionsNoState(sw, dTags, lAdditionalPredicates);
                WriteTaggedPredicatesNoState(sw, lAdditionalPredicates);
                foreach (Action aKnowWhether in lAllActions)
                    WriteConditionalAction(sw, aKnowWhether);
                sw.WriteLine();
                
                //WriteReasoningActionsNoState(sw, dTags, pCurrent);
            }
            else
            {
                WriteTaggedPredicatesNoState(sw, null);
                sw.WriteLine();
                WriteKnowledgeActionsNoState(sw, dTags);
                //WriteReasoningActionsNoState(sw, dTags, pCurrent);
            }


            sw.WriteLine(")");
            sw.Close();
        }

        public void WriteTaggedDomain(string sFileName, Dictionary<string, List<Predicate>> dTags, Problem pCurrent)
        {
            if (HasNonDeterministicActions() && m_bUseOptions)
            {
                Domain dDeterministic = RemoveNonDeterministicEffects();
                dDeterministic.WriteTaggedDomain(sFileName, dTags, pCurrent);
                return;
            }


            StreamWriter sw = new StreamWriter(sFileName);
            sw.WriteLine("(define (domain K" + Name + ")");


            sw.WriteLine("(:requirements :strips :typing)");

            WriteFunctions(sw);
            WriteTypes(sw, true);
            WriteConstants(sw, dTags);
            sw.WriteLine();


            if (SDRPlanner.SplitConditionalEffects)
            {
                List<Predicate> lAdditionalPredicates = new List<Predicate>();
                List<Action> lAllActions = GetKnowledgeActions(sw, dTags, lAdditionalPredicates);
                WriteTaggedPredicates(sw, lAdditionalPredicates);
                foreach (Action aKnowWhether in lAllActions)
                    WriteConditionalAction(sw, aKnowWhether);
                sw.WriteLine();

                WriteReasoningActions(sw, dTags, pCurrent);
            }
            else
            {
                WriteTaggedPredicates(sw, null);
                sw.WriteLine();
                WriteKnowledgeActions(sw, dTags);
                WriteReasoningActions(sw, dTags, pCurrent);
            }




            if (RemoveConflictingConditionalEffects)
                WriteAxiomsActions(sw, dTags);

            sw.WriteLine(")");
            sw.Close();
        }

        private void WriteFunctions(StreamWriter sw)
        {
            if (Functions.Count > 0)
            {
                sw.Write("(:functions");
                foreach (string sFunction in Functions)
                    sw.Write(" " + sFunction);
                sw.WriteLine(")");

            }
        }

        private Domain RemoveNonDeterministicEffects()
        {
            Domain dDeterministic = new Domain(Name, Path);
            dDeterministic.Predicates = new List<Predicate>(Predicates);
            dDeterministic.Constants = new List<Constant>(Constants);
            dDeterministic.Types = new List<string>(Types);
            dDeterministic.Actions = new List<Action>();
            dDeterministic.m_lAlwaysKnown = m_lAlwaysKnown;
            dDeterministic.m_lAlwaysConstant = m_lAlwaysConstant;
            dDeterministic.m_dConstantNameToType = m_dConstantNameToType;
            dDeterministic.Functions = Functions;

            dDeterministic.Types.Add(Domain.OPTION);
            dDeterministic.m_lAlwaysConstant.Add(Domain.OPTION_PREDICATE);
            //dDeterministic.m_lAlwaysKnown.Add(Domain.OPTION_PREDICATE);

            ParametrizedPredicate ppOption = new ParametrizedPredicate(Domain.OPTION_PREDICATE);
            ppOption.AddParameter(new Parameter(OPTION, "?o"));
            dDeterministic.Predicates.Add(ppOption);

            int cOptions = Math.Max(MaxNonDeterministicEffects(), MAX_OPTIONS);
            for (int iOption = 0; iOption < cOptions; iOption++)
            {
                dDeterministic.Constants.Add(new Constant(OPTION, "opt" + iOption));
            }

            foreach (Action a in Actions)
            {
                if (a.ContainsNonDeterministicEffect)
                {
                    Action aDeterministic = a.ReplaceNonDeterministicEffectsWithOptions(m_lAlwaysKnown, MAX_OPTIONS);
                    dDeterministic.Actions.Add(aDeterministic);
                }
                else
                {
                    dDeterministic.Actions.Add(a);
                }
            }

            return dDeterministic;
        }

        private string GeneratePredicateAxiom(GroundedPredicate gp, string sPrefix, string sAdditionalConstants)
        {
            string sGiven = "(Not-" + sPrefix + gp.Name;
            foreach (Constant p in gp.Constants)
                sGiven += " " + p.Name;
            sGiven += sAdditionalConstants;
            sGiven += ")";
            string sEffect = "(and (not " + sGiven + ")";
            sEffect += " (not ";
            sEffect += "(" + sPrefix + gp.Name;
            foreach (Constant p in gp.Constants)
                sEffect += " " + p.Name;
            sEffect += sAdditionalConstants;
            sEffect += ")))";
            string s = "(when " + sGiven + " " + sEffect + ")";
            return s;
        }

        private void WriteAxiomsAction(StreamWriter sw, Dictionary<string, List<Predicate>> dTags)
        {
            sw.WriteLine("(:action apply-axioms");
            sw.WriteLine("\t:precondition (not (axioms-applied))\n");
            sw.WriteLine("\t:effect (and (axioms-applied)\n");

            HashSet<GroundedPredicate> lGrounded = GroundAllPredicates();
            foreach (GroundedPredicate pp in lGrounded)
            {
                sw.WriteLine("\t\t" + GeneratePredicateAxiom(pp, "", ""));

                if (!AlwaysKnown(pp))
                {
                    sw.WriteLine("\t\t" + GeneratePredicateAxiom(pp, "K", " " + TRUE_VALUE));
                    sw.WriteLine("\t\t" + GeneratePredicateAxiom(pp, "K", " " + FALSE_VALUE));

                    foreach (string sTag in dTags.Keys)
                    {
                        sw.WriteLine("\t\t" + GeneratePredicateAxiom(pp, "KGiven", " " + sTag + " " + TRUE_VALUE));
                        sw.WriteLine("\t\t" + GeneratePredicateAxiom(pp, "KGiven", " " + sTag + " " + FALSE_VALUE));

                    }
                }
            }
            sw.WriteLine("))");
        }


        private void WriteAxiomsActions(StreamWriter sw, Dictionary<string, List<Predicate>> dTags)
        {

            HashSet<GroundedPredicate> lGrounded = GroundAllPredicates();
            foreach (GroundedPredicate gp in lGrounded)
            {
                sw.WriteLine("(:action apply-axioms-" + gp.Name);
                sw.WriteLine("\t:precondition (not (axioms-applied))");
                sw.WriteLine("\t:effect (and ");

                sw.Write("(axioms-applied-" + gp.Name);
                foreach (Constant c in gp.Constants)
                    sw.Write("-" + c.Name);
                sw.WriteLine(")");


                sw.WriteLine("\t\t" + GeneratePredicateAxiom(gp, "", ""));

                if (!AlwaysKnown(gp))
                {
                    sw.WriteLine("\t\t" + GeneratePredicateAxiom(gp, "K", " " + TRUE_VALUE));
                    sw.WriteLine("\t\t" + GeneratePredicateAxiom(gp, "K", " " + FALSE_VALUE));

                    foreach (string sTag in dTags.Keys)
                    {
                        sw.WriteLine("\t\t" + GeneratePredicateAxiom(gp, "KGiven", " " + sTag + " " + TRUE_VALUE));
                        sw.WriteLine("\t\t" + GeneratePredicateAxiom(gp, "KGiven", " " + sTag + " " + FALSE_VALUE));

                    }
                }
                sw.WriteLine("))");
            }
            sw.WriteLine("(:action apply-axioms");
            sw.WriteLine("\t:precondition (and (not (axioms-applied))");
            foreach (GroundedPredicate gp in lGrounded)
            {
                sw.Write("\t\t(axioms-applied-" + gp.Name);
                foreach (Constant c in gp.Constants)
                    sw.Write("-" + c.Name);
                sw.WriteLine(")");
            }
            sw.WriteLine(")");
            sw.WriteLine("\t:effect (and (axioms-applied)");
            foreach (GroundedPredicate gp in lGrounded)
            {
                sw.Write("\t\t(not (axioms-applied-" + gp.Name);
                foreach (Constant c in gp.Constants)
                    sw.Write("-" + c.Name);
                sw.WriteLine("))");
            }
            sw.WriteLine("))");

        }

        private void WriteKnowledgePreconditions(StreamWriter sw, Action pa, List<Predicate> lKnow)
        {
            HashSet<Predicate> lPredicates = new HashSet<Predicate>();
            pa.Preconditions.GetAllPredicates(lPredicates);
            CompoundFormula cfAnd = new CompoundFormula("and");
            cfAnd.AddOperand(pa.Preconditions.Simplify());

            foreach (Predicate p in lPredicates)
            {
                if (lKnow == null || lKnow.Contains(p))
                {
                    cfAnd.AddOperand(new PredicateFormula(new KnowPredicate(p)));
                }
            }
            sw.WriteLine(":precondition " + cfAnd);

            /*
            sw.Write(":precondition (and");
            foreach (Formula f in cfAnd.Operands)
                sw.Write(" " + f.ToString());
            foreach (Predicate p in lPredicates)
            {
                if (lKnow == null || lKnow.Contains(p))
                {
                    WriteKnowledgePredicate(sw, p);
                }
            }
            
            sw.WriteLine(")");
             * */

        }

        public void WriteKnowledgePredicate(StreamWriter sw, Predicate p)
        {
            if (!AlwaysKnown(p))
                sw.Write(new KnowPredicate(p).ToString());
        }
        private void WriteKnowledgeEffects(StreamWriter sw, Action pa, List<Predicate> lKnow)
        {
            HashSet<Predicate> lPredicates = new HashSet<Predicate>();
            if( pa.Effects != null )
                pa.Effects.GetAllPredicates(lPredicates);
            if( pa.Observe != null )
                pa.Observe.GetAllPredicates(lPredicates);
            CompoundFormula cfAnd = (CompoundFormula)pa.Effects;
            if (cfAnd != null && cfAnd.Operator != "and")
                throw new NotImplementedException();
            sw.Write(":effect (and");
            if (cfAnd != null)
            {
                foreach (Formula f in cfAnd.Operands)
                    sw.Write(" " + f.ToString());
            }
            foreach (Predicate p in lPredicates)
            {
                if (lKnow == null || lKnow.Contains(p))
                {
                    WriteKnowledgePredicate(sw, p);
                }
            }
            sw.WriteLine(")");
        }

        private void WriteKnowledgeAction(StreamWriter sw, Action a)
        {
            sw.WriteLine("(:action " + a.Name);
            if (a is ParametrizedAction)
            {
                ParametrizedAction pa = (ParametrizedAction)a;
                sw.Write(":parameters (");
                foreach (Parameter p in pa.Parameters)
                    sw.Write(" " + p.FullString());
                sw.WriteLine(")");
            }
            if (a.Preconditions != null)
                WriteKnowledgePreconditions(sw, a, null);
            WriteKnowledgeEffects(sw, a, null);

            sw.WriteLine(")");
            sw.WriteLine();
        }


        private void WriteAction(StreamWriter sw, Action a)
        {
            if (RemoveConflictingConditionalEffects)
                RemoveConflictingConditionalEffectsFromAction(a);

            sw.WriteLine("(:action " + a.Name);
            if (a is ParametrizedAction)
            {
                ParametrizedAction pa = (ParametrizedAction)a;
                sw.Write(":parameters (");
                foreach (Parameter p in pa.Parameters)
                    sw.Write(" " + p.FullString());
                sw.WriteLine(")");
            }
            if (a.Preconditions != null)
                sw.WriteLine(":precondition " + a.Preconditions);
            sw.WriteLine(":effect " + a.Effects);

            sw.WriteLine(")");
            sw.WriteLine();
        }

        private void WriteSensor(StreamWriter sw, Action a)
        {
            Debug.Assert(a.Observe != null && a.Effects == null);
            sw.WriteLine("(:sensor " + a.Name);
            if (a is ParametrizedAction)
            {
                ParametrizedAction pa = (ParametrizedAction)a;
                sw.Write(":parameters (");
                foreach (Parameter p in pa.Parameters)
                    sw.Write(" " + p.FullString());
                sw.WriteLine(")");
            }
            if (a.Preconditions != null)
                sw.WriteLine(":condition " + a.Preconditions);
            sw.WriteLine(":sensed " + a.Observe);

            sw.WriteLine(")");
            sw.WriteLine();
        }

        private void WriteConditionalSplitAction(StreamWriter sw, Action a, List<Predicate> lKnow)
        {
            sw.WriteLine("(:action " + a.Name);
            if (a is ParametrizedAction)
            {
                ParametrizedAction pa = (ParametrizedAction)a;
                sw.Write(":parameters (");
                foreach (Parameter p in pa.Parameters)
                    sw.Write(" " + p.FullString());
                sw.WriteLine(")");
            }
            if (a.Preconditions != null)
                WriteKnowledgePreconditions(sw, a, lKnow);
            WriteKnowledgeEffects(sw, a, lKnow);

            sw.WriteLine(")");
            sw.WriteLine();
        }
/*
        private void WriteKnowledgeActions(StreamWriter sw)
        {
            foreach (Action a in Actions)
            {
                if (!a.HasConditionalEffects)
                    WriteKnowledgeAction(sw, a);
                else
                {
                    //BUGBUG - ff supports conditional effects
                    CompoundFormula cfObligatory = null;
                    List<Action> lSplit = a.SplitConditionalEffects(out cfObligatory);
                    List<Predicate> lKnow = new List<Predicate>();
                    cfObligatory.GetAllPredicates(lKnow);
                    if (a.Preconditions != null)
                        a.Preconditions.GetAllPredicates(lKnow);
                    foreach (Action aSplit in lSplit)
                        WriteConditionalSplitAction(sw, aSplit, lKnow);
                }
            }
        }
*/

        public List<Action> GetAllKnowledgeActions(Dictionary<string, List<Predicate>> dTags)
        {
            List<Action> lActions = new List<Action>();
            foreach (Action a in Actions)
            {
                if (a.Effects == null & a.Observe != null)
                {
                    Action aObserveTrue = a.NonConditionalObservationTranslation(dTags, m_lAlwaysKnown, true);
                    lActions.Add(aObserveTrue);
                    Action aObserveFalse = a.NonConditionalObservationTranslation(dTags, m_lAlwaysKnown, false);
                    lActions.Add(aObserveFalse);
                }

                else
                {
                    Action aKnowledge = a.AddTaggedConditions(dTags, m_lAlwaysKnown);
                    lActions.Add(aKnowledge);
                }
            }
            return lActions;
        }
        public List<Action> GetAllReasoningActions(Dictionary<string, List<Predicate>> dTags)
        {
            List<Action> lActions = new List<Action>();
            //get merges and tag refutation
            foreach (ParametrizedPredicate pp in Predicates)
            {
                if (!AlwaysKnown(pp))
                {
                    Action aMerge = GenerateMergeAction(pp, dTags);
                    lActions.Add(aMerge);
                    Action aRefute = GenerateRefutationAction(pp, true);
                    lActions.Add(aRefute);
                    aRefute = GenerateRefutationAction(pp, false);
                    lActions.Add(aRefute);
                }
            }
            return lActions;
        }

        private List<Action> GetKnowledgeActionsNoState(StreamWriter sw, Dictionary<string, List<Predicate>> dTags, List<Predicate> lAdditionalPredicates)
        {
            List<Action> lAllActions = new List<Action>();
            lAdditionalPredicates.Add(new GroundedPredicate("NotInAction"));

            foreach (Action a in Actions)
            {
                if (a.Effects == null && a.Observe != null)
                {
                    List<Action> lKnowWhether = a.TagObservationTranslationNoState(dTags, this);
                    lAllActions.AddRange(lKnowWhether);
                }
                else
                {
                    List<Action> lKnowWhether = a.TagCompilationNoState(dTags, this, lAdditionalPredicates);
                    lAllActions.AddRange(lKnowWhether);
                }
            }
            return lAllActions;
        }



        private List<Action> GetKnowledgeActions(StreamWriter sw, Dictionary<string, List<Predicate>> dTags, List<Predicate> lAdditionalPredicates)
        {
            List<Action> lAllActions = new List<Action>();
            lAdditionalPredicates.Add(new GroundedPredicate("NotInAction"));

            foreach (Action a in Actions)
            {
                if (a.Effects == null && a.Observe != null)
                {
                    Action aObserveTrue = a.NonConditionalObservationTranslation(dTags, m_lAlwaysKnown, true);
                    Action aObserveFalse = a.NonConditionalObservationTranslation(dTags, m_lAlwaysKnown, false);
                    lAllActions.Add(aObserveTrue);
                    lAllActions.Add(aObserveFalse);
                }
                else
                {
                    List<Action> lCompiled = a.KnowCompilationSplitConditions(dTags, m_lAlwaysKnown, lAdditionalPredicates);
                    lAllActions.AddRange(lCompiled);
                }
            }
            return lAllActions;
        }

        private void WriteKnowledgeActionsNoState(StreamWriter sw, Dictionary<string, List<Predicate>> dTags)
        {
            int cTranslatedActions = 0;
            foreach (Action a in Actions)
            {
                if (a.Effects == null && a.Observe != null)
                {
                    List<Action> lCompiled = a.TagObservationTranslationNoState(dTags, this);
                    foreach (Action aKnowWhether in lCompiled)
                        WriteConditionalAction(sw, aKnowWhether);
                }
                else
                {
                    List<Action> lCompiled = a.TagCompilationNoState(dTags, this, null);
                    foreach (Action aCompiled in lCompiled)
                    {
                        cTranslatedActions++;
                        WriteConditionalAction(sw, aCompiled);
                    }
                }
            }
        }


/*
        private void WriteKnowledgeActionsNoState(StreamWriter sw, Dictionary<string, List<Predicate>> dTags)
        {
            int  cTranslatedActions = 0;
            int cMaxTranslatedConditionalEffects = 0, cMaxOriginalConditionalEffects = 0;
            foreach (Action a in Actions)
            {
                //if (a.GetConditions().Count > cMaxOriginalConditionalEffects)
                //    cMaxOriginalConditionalEffects = a.GetConditions().Count;


                if (a.Effects == null && a.Observe != null)
                {
                    //Action aKnow = a.KnowObservationTranslation();
                    //WriteConditionalAction(sw, aKnow);
                    BUGBUG;
                    List<Action> lKnowWhether = a.KnowWhetherTagObservationTranslation(dTags, this);
                    foreach (Action aKnowWhether in lKnowWhether)
                        WriteConditionalAction(sw, aKnowWhether);
                }
                else
                {
                    //Action aKnow = a.KnowCompilation(dTags, this);
                    //WriteConditionalAction(sw, aKnow);
                    List<Action> lKnowWhether = a.KnowWhetherTagCompilation(dTags, this);
                    foreach (Action aKnowWhether in lKnowWhether)
                    {
                        cTranslatedActions++;
                        //if (aKnowWhether.GetConditions().Count > cMaxTranslatedConditionalEffects)
                        //    cMaxTranslatedConditionalEffects = aKnowWhether.GetConditions().Count;
                        WriteConditionalAction(sw, aKnowWhether);
                    }
                }
            }
            //Console.WriteLine("Original: #Actions " + Actions.Count + ", Max conditions " + cMaxOriginalConditionalEffects);
            //Console.WriteLine("Translated: #Actions " + cTranslatedActions + ", Max conditions " + cMaxTranslatedConditionalEffects);
        }
*/

        private void WriteKnowledgeActions(StreamWriter sw, Dictionary<string, List<Predicate>> dTags)
        {
            foreach (Action a in Actions)
            {
                if (a.ContainsNonDeterministicEffect)
                {
                    if (m_bReplaceNonDeterministicEffectsWithOptions)
                    {
                        Action aDeterministic = a.ReplaceNonDeterministicEffectsWithOptions(m_lAlwaysKnown);
                        Action aKnowledge = aDeterministic.AddTaggedConditions(dTags, m_lAlwaysKnown);
                        WriteConditionalAction(sw, aKnowledge);
                    }
                    else
                    {
                        List<Action> lKnowledgeActions = a.AddTaggedNonDeterministicConditions(dTags, m_lAlwaysKnown);
                        foreach (Action aKnowledge in lKnowledgeActions)
                            WriteConditionalAction(sw, aKnowledge);
                    }
                }
                 
                else if (a.Effects == null & a.Observe != null)
                {
                    Action aObserveTrue = a.NonConditionalObservationTranslation(dTags, m_lAlwaysKnown, true);
                    WriteConditionalAction(sw, aObserveTrue);
                    Action aObserveFalse = a.NonConditionalObservationTranslation(dTags, m_lAlwaysKnown, false);
                    WriteConditionalAction(sw, aObserveFalse);
                }
                    
                else
                {
                    Action aKnowledge = a.AddTaggedConditions(dTags, m_lAlwaysKnown);
                    WriteConditionalAction(sw, aKnowledge);
                }
                /* I can't split the effects like that becuase if KC/t -> KE/t even if C is not true
                if (a.HasConditionalEffects)
                {
                    List<Action> aSplitted = a.SplitTaggedConditions(dTags, m_lAlwaysKnown);
                    foreach (Action aKnowledge in aSplitted)
                        WriteConditionalAction(sw, aKnowledge);
                }
                else
                {
                    Action aKnowledge = a.AddKnowledge(m_lAlwaysKnown);
                    WriteConditionalAction(sw, aKnowledge);
                }
                 * */
            }
        }
        private void WriteReasoningActions(StreamWriter sw, Dictionary<string, List<Predicate>> dTags, Problem pCurrent)
        {
            //write merges and tag refutation
            foreach (ParametrizedPredicate pp in Predicates)
            {
                if (!AlwaysKnown(pp))
                {
                    Action aMerge = GenerateMergeAction(pp, dTags);
                    WriteAction(sw, aMerge);
                    Action aRefute = GenerateRefutationAction(pp, true);
                    WriteAction(sw, aRefute);
                    aRefute = GenerateRefutationAction(pp, false);
                    WriteAction(sw, aRefute);
                    
                    //Action aAssert = GenerateAssertInvalid(pp, pCurrent.Goal);
                    //WriteAction(sw, aAssert);
                }
                /*
                List<Action> lRefutation = GenerateRefutationActions(pp, dTags);
                foreach (Action aRefute in lRefutation)
                    WriteAction(sw, aRefute);
                 * */
            }
        }

        private void WriteReasoningActionsNoState(StreamWriter sw, Dictionary<string, List<Predicate>> dTags, Problem pCurrent)
        {
            List<List<string>[]> lAllPartitions = new List<List<string>[]>();
            Action.GetAllPartitions(new List<string>(dTags.Keys), lAllPartitions);
            //write merges and tag refutation
            foreach (ParametrizedPredicate pp in Predicates)
            {
                if (!(AlwaysKnown(pp) && AlwaysConstant(pp)) && pp.Name != OPTION_PREDICATE)
                {
                    Action aMerge = null;
                    //aMerge = GenerateKnowMergeAction(pp, this, dTags, true, false);
                    //WriteAction(sw, aMerge);
                    //aMerge = GenerateKnowMergeAction(pp, this, dTags, false, false);
                    //WriteAction(sw, aMerge);
                    /* this allows the planner to cheat somehow - not sure how but it does
                    aMerge = GenerateKnowUnMergeAction(pp, dTags, true);
                    WriteAction(sw, aMerge);
                    aMerge = GenerateKnowUnMergeAction(pp, dTags, false);
                    WriteAction(sw, aMerge);
                     * */
                    if (!AlwaysKnown(pp))
                    {
                        //aMerge = GenerateKnowMergeAction(pp, this, dTags, true, true);
                        //WriteAction(sw, aMerge);
                        //aMerge = GenerateKnowUnMergeAction(pp, dTags, true, false);
                        //WriteAction(sw, aMerge);
                        //aMerge = GenerateKnowUnMergeAction(pp, dTags, false, false);
                        //WriteAction(sw, aMerge);
                        //aMerge = GenerateKnowUnMergeAction(pp, dTags, true, true);
                        //WriteAction(sw, aMerge);
                    }


                    if (!AlwaysKnown(pp))
                    {
                        foreach (List<string>[] aPartition in lAllPartitions)
                        {
                            aMerge = GenerateTagMergeAction(pp, aPartition[0], aPartition[1], true);
                            WriteAction(sw, aMerge);
                            aMerge = GenerateTagMergeAction(pp, aPartition[0], aPartition[1], false);
                            WriteAction(sw, aMerge);
                        }
                    }
                    if(Observable(pp))
                    {
                        Action aRefute = GenerateTagRefutationGiven(pp, dTags);
                        WriteAction(sw, aRefute);
                    }
                }
            }
        }

        private bool Observable(ParametrizedPredicate pp)
        {
            foreach (Action a in Actions)
            {
                if (a.Observe != null)
                {
                    HashSet<Predicate> lObservables = a.Observe.GetAllPredicates();
                    foreach(Predicate p in lObservables)
                    {
                        if (p.Name == pp.Name)
                            return true;
                    }

                }
            }
            return false;
        }

        private Action GenerateTagMergeAction(ParametrizedPredicate pp, List<string> lIncludedTags, List<string> lExcludedTags, bool bValue)
        {
            string sName = "TagMerge-" + pp.Name;
            foreach (string sTag in lIncludedTags)
                sName += "-" + sTag;
            if (bValue == true)
                sName += "-T";
            else
                sName += "-F";
            ParametrizedAction pa = new ParametrizedAction(sName);
            foreach (Parameter param in pp.Parameters)
                pa.AddParameter(param);
            CompoundFormula cfAnd = new CompoundFormula("and");

            foreach (string sTag in lIncludedTags)
            {
                ParametrizedPredicate ppKGivenT = (ParametrizedPredicate)pp.GenerateGiven(sTag);
                foreach (Parameter p in ppKGivenT.Parameters)
                    if (p.Type == VALUE)
                        p.Name = VALUE_PARAMETER;

                if (bValue == true)
                    cfAnd.AddOperand(ppKGivenT);
                else
                    cfAnd.AddOperand(ppKGivenT.Negate());

                if (sTag != lIncludedTags[0])
                {
                    ParametrizedPredicate pKNotT = new ParametrizedPredicate("KNot");
                    pKNotT.AddParameter(new Constant(TAG, sTag));
                    pKNotT.AddParameter(new Constant(TAG, lIncludedTags[0]));
                    cfAnd.AddOperand(pKNotT.Negate());
                }
            }
            foreach (string sTag in lExcludedTags)
            {
                ParametrizedPredicate ppKGivenT = (ParametrizedPredicate)pp.GenerateGiven(sTag);
                foreach (Parameter p in ppKGivenT.Parameters)
                    if (p.Type == VALUE)
                        p.Name = VALUE_PARAMETER;
                ParametrizedPredicate pKNotT = new ParametrizedPredicate("KNot");
                pKNotT.AddParameter(new Constant(TAG, sTag));
                pKNotT.AddParameter(new Constant(TAG, lIncludedTags[0]));
                cfAnd.AddOperand(pKNotT);
            }
            if (SDRPlanner.SplitConditionalEffects)
                cfAnd.AddOperand(new GroundedPredicate("NotInAction"));
            pa.Preconditions = cfAnd;
            cfAnd = new CompoundFormula("and");
            foreach (string sTag in lIncludedTags)
            {
                Predicate ppK = pp.GenerateKnowGiven(sTag, true);
                cfAnd.AddOperand(ppK);
            }
            
            pa.SetEffects(cfAnd);
            return pa;
        }


        private Action GenerateTagMergeAction(ParametrizedPredicate pp, Dictionary<string, List<Predicate>> dTags, bool bValue)
        {
            string sName = "TagMerge-" + pp.Name;
            if (bValue == true)
                sName += "-T";
            else
                sName += "-F";
            ParametrizedAction pa = new ParametrizedAction(sName);
            foreach (Parameter param in pp.Parameters)
                pa.AddParameter(param);
            Parameter pTag = new Parameter(TAG, TAG_PARAMETER);
            pa.AddParameter(pTag);
            CompoundFormula cfAnd = new CompoundFormula("and");

            foreach (string sTag in dTags.Keys)
            {
                CompoundFormula cfOr = new CompoundFormula("or");
                ParametrizedPredicate ppKGivenT = (ParametrizedPredicate)pp.GenerateGiven(sTag);
                foreach (Parameter p in ppKGivenT.Parameters)
                    if (p.Type == VALUE)
                        p.Name = VALUE_PARAMETER;

                ParametrizedPredicate pKNotT = new ParametrizedPredicate("KNot");
                pKNotT.AddParameter(new Constant(TAG, sTag));
                pKNotT.AddParameter(pTag);
                if (bValue == true)
                    cfOr.AddOperand(ppKGivenT);
                else
                    cfOr.AddOperand(ppKGivenT.Negate());
                cfOr.AddOperand(pKNotT);
                cfAnd.AddOperand(cfOr);
            }
            pa.Preconditions = cfAnd;
            cfAnd = new CompoundFormula("and");
            Predicate ppK = pp.GenerateKnowGiven(TAG_PARAMETER, true);
            cfAnd.AddOperand(ppK);
            pa.SetEffects( cfAnd);
            return pa;
        }

        private Action GenerateTagRefutationGiven(ParametrizedPredicate pp, Dictionary<string, List<Predicate>> dTags)
        {
            ParametrizedAction pa = new ParametrizedAction("Refute-" + pp.Name);
            foreach (Parameter param in pp.Parameters)
                pa.AddParameter(param);
            Parameter pTag1 = new Parameter(TAG, TAG_PARAMETER + "1");
            pa.AddParameter(pTag1);
            Parameter pTag2 = new Parameter(TAG, TAG_PARAMETER + "2");
            pa.AddParameter(pTag2);
            CompoundFormula cfAnd = new CompoundFormula("and");

            cfAnd.AddOperand(pp.GenerateGiven(TAG_PARAMETER + "1"));
            cfAnd.AddOperand(pp.Negate().GenerateGiven(TAG_PARAMETER + "2"));
            cfAnd.AddOperand(pp.GenerateKnowGiven(TAG_PARAMETER + "1", true));
            cfAnd.AddOperand(pp.GenerateKnowGiven(TAG_PARAMETER + "2", true));

            if (SDRPlanner.SplitConditionalEffects)
                cfAnd.AddOperand(new GroundedPredicate("NotInAction"));

            pa.Preconditions = cfAnd;
            cfAnd = new CompoundFormula("and");
            ParametrizedPredicate ppKnowNot1Given2 = new ParametrizedPredicate("KNot");
            ppKnowNot1Given2.AddParameter(pTag1);
            ppKnowNot1Given2.AddParameter(pTag2);
            cfAnd.AddOperand(ppKnowNot1Given2);
            ParametrizedPredicate ppKnowNot2Given1 = new ParametrizedPredicate("KNot");
            ppKnowNot2Given1.AddParameter(pTag2);
            ppKnowNot2Given1.AddParameter(pTag1);
            cfAnd.AddOperand(ppKnowNot2Given1);

            pa.SetEffects( cfAnd);
            return pa;
        }


        private Action GenerateMergeAction(ParametrizedPredicate pp, Dictionary<string, List<Predicate>> dTags)
        {
            ParametrizedAction pa = new ParametrizedAction("Merge-" + pp.Name);
            foreach (Parameter param in pp.Parameters)
                pa.AddParameter(param);
            Parameter pValue = new Parameter(Domain.VALUE, VALUE_PARAMETER);
            pa.AddParameter(pValue);
            CompoundFormula cfAnd = new CompoundFormula("and");
            /*
            ParametrizedPredicate ppK = new ParametrizedPredicate("K" + pp.Name);
            foreach (Parameter param in pp.Parameters)
                ppK.AddParameter(param);
             */
            KnowPredicate ppK = new KnowPredicate(pp);
            ppK.Parametrized = true;
            cfAnd.AddOperand(ppK.Negate());//add ~know p to the preconditions - no point in activating merge when we know p

            if (SDRPlanner.SplitConditionalEffects)
                cfAnd.AddOperand(new GroundedPredicate("NotInAction"));

            foreach (string sTag in dTags.Keys)
            {
                CompoundFormula cfOr = new CompoundFormula("or");
                ParametrizedPredicate ppKGivenT = new ParametrizedPredicate("KGiven" + pp.Name);
                GroundedPredicate pKNotT = new GroundedPredicate("KNot");
                pKNotT.AddConstant(new Constant(TAG, sTag));
                foreach (Parameter param in pp.Parameters)
                    ppKGivenT.AddParameter(param);
                ppKGivenT.AddParameter(new Constant(TAG, sTag));
                ppKGivenT.AddParameter(pValue);
                cfOr.AddOperand(new PredicateFormula(ppKGivenT));
                cfOr.AddOperand(new PredicateFormula(pKNotT));
                cfAnd.AddOperand(cfOr);
            }
            pa.Preconditions = cfAnd;
            cfAnd = new CompoundFormula("and");
            cfAnd.AddOperand(ppK);
            pa.SetEffects( cfAnd);
            return pa;
        }

        private Action GenerateKnowMergeAction(ParametrizedPredicate pp, Domain d, Dictionary<string, List<Predicate>> dTags, bool bValue, bool bKnowWhether)
        {
            ParametrizedAction pa = null;
            string sName = "";
            if (bKnowWhether)
            {
                sName = "Merge-KW-" + pp.Name;
            }
            else
            {
                sName = "Merge-K-" + pp.Name;
                if (bValue == true)
                    sName += "-T";
                else
                    sName += "-F";
            }
            pa = new ParametrizedAction(sName);
            foreach (Parameter param in pp.Parameters)
                pa.AddParameter(param);
            CompoundFormula cfAnd = new CompoundFormula("and");
            Predicate ppK = null;
            if (bKnowWhether)
            {
                ppK = new KnowWhetherPredicate(pp);
            }
            else
            {
                ppK = new KnowPredicate(pp, bValue, false);
            }
            cfAnd.AddOperand(ppK.Negate());//add ~know p to the preconditions - no point in activating merge when we know p
            foreach (string sTag in dTags.Keys)
            {
                ParametrizedPredicate ppKGivenT = null;
                if (bKnowWhether)
                    ppKGivenT = new ParametrizedPredicate("KWGiven" + pp.Name);
                else
                {
                    ppKGivenT = new ParametrizedPredicate("Given" + pp.Name);
                }
                foreach (Parameter param in pp.Parameters)
                    ppKGivenT.AddParameter(param);
                ppKGivenT.AddParameter(new Constant(TAG, sTag));
                if(!bKnowWhether && bValue == false)
                    cfAnd.AddOperand(ppKGivenT.Negate());
                else
                    cfAnd.AddOperand(ppKGivenT);
            }
            pa.Preconditions = cfAnd;
            cfAnd = new CompoundFormula("and");
            cfAnd.AddOperand(ppK);
            if (!bKnowWhether && !d.AlwaysKnown(pp))
                cfAnd.AddOperand(new KnowWhetherPredicate(pp));
            pa.SetEffects( cfAnd);
            return pa;
        }

        private Action GenerateKnowUnMergeAction(ParametrizedPredicate pp, Dictionary<string, List<Predicate>> dTags, bool bValue, bool bKnowWhether)
        {
            ParametrizedAction pa = null;
            if (bKnowWhether)
                pa = new ParametrizedAction("UnMerge-KW-" + pp.Name);
            else
                pa = new ParametrizedAction("UnMerge-K-" + pp.Name);
            foreach (Parameter param in pp.Parameters)
                pa.AddParameter(param);
            CompoundFormula cfAnd = new CompoundFormula("and");
            Predicate ppK = null;
            if (bKnowWhether)
            {
                ppK = new KnowWhetherPredicate(pp);
            }
            else
            {
                ppK = new KnowPredicate(pp, bValue, false);
            }
            foreach (string sTag in dTags.Keys)
            {
                ParametrizedPredicate ppKGivenT = null;
                if (bKnowWhether)
                    ppKGivenT = new ParametrizedPredicate("KWGiven" + pp.Name);
                else
                    ppKGivenT = new ParametrizedPredicate("Given" + pp.Name);
                foreach (Parameter param in pp.Parameters)
                    ppKGivenT.AddParameter(param);
                ppKGivenT.AddParameter(new Constant(TAG, sTag));
                if (!bKnowWhether && bValue == false)
                {
                    cfAnd.AddOperand(ppKGivenT.Negate());
                }
                else
                    cfAnd.AddOperand(ppKGivenT);
            }
            pa.SetEffects( cfAnd);
            cfAnd = new CompoundFormula("and");
            cfAnd.AddOperand(ppK);
            pa.Preconditions = cfAnd;
            return pa;
        }

        private Action GenerateKnowUnMergeAction(ParametrizedPredicate pp, Dictionary<string, List<Predicate>> dTags, bool bValue)
        {
            string sName = "UnMerge-K-" + pp.Name;
            if (bValue)
                sName += "-T";
            else
                sName += "-F";
            ParametrizedAction pa = new ParametrizedAction(sName);
            foreach (Parameter param in pp.Parameters)
                pa.AddParameter(param);

            CompoundFormula cfAnd = new CompoundFormula("and");
            Predicate ppK = new KnowPredicate(pp, bValue, false);
            
            foreach (string sTag in dTags.Keys)
            {
                ParametrizedPredicate ppKGivenT = new ParametrizedPredicate("Given" + pp.Name);
                foreach (Parameter param in pp.Parameters)
                    ppKGivenT.AddParameter(param);
                ppKGivenT.AddParameter(new Constant(TAG, sTag));
                if (bValue == false)
                {
                    cfAnd.AddOperand(ppKGivenT.Negate());
                }
                else
                    cfAnd.AddOperand(ppKGivenT);
            }
            pa.SetEffects( cfAnd);
            cfAnd = new CompoundFormula("and");
            cfAnd.AddOperand(ppK);
            pa.Preconditions = cfAnd;
            return pa;
        }

        private Action GenerateRefutationAction(ParametrizedPredicate pp, bool bValue)
        {
            string sName = "Refute";
            if (bValue)
                sName += "T";
            else
                sName += "F";
            sName += "-" + pp.Name;
            ParametrizedAction pa = new ParametrizedAction(sName);
            Parameter pTag = new Parameter(TAG, TAG_PARAMETER);
            foreach (Parameter param in pp.Parameters)
                pa.AddParameter(param);
            pa.AddParameter(pTag);
            CompoundFormula cfAnd = new CompoundFormula("and");
            ParametrizedPredicate ppKGivenT = new ParametrizedPredicate("KGiven" + pp.Name);
            foreach (Parameter param in pp.Parameters)
                ppKGivenT.AddParameter(param);
            ppKGivenT.AddParameter(pTag);
            if (bValue)
                ppKGivenT.AddParameter(new Constant(Domain.VALUE, Domain.TRUE_VALUE));
            else
                ppKGivenT.AddParameter(new Constant(Domain.VALUE, Domain.FALSE_VALUE));

            ParametrizedPredicate pKNotT = new ParametrizedPredicate("KNot");
            pKNotT.AddParameter(pTag);
            cfAnd.AddOperand(pKNotT.Negate());//add ~know not t - if we already know that t is false there is no point in running tag refutation

            if (SDRPlanner.SplitConditionalEffects)
                cfAnd.AddOperand(new GroundedPredicate("NotInAction"));

            /*
            ParametrizedPredicate ppK = new ParametrizedPredicate("K" + pp.Name);
            foreach (Parameter param in pp.Parameters)
                ppK.AddParameter(param);
            */
            KnowPredicate ppK = new KnowPredicate(pp, !bValue, false);
            cfAnd.AddOperand(ppKGivenT);
            cfAnd.AddOperand(ppK);

            if (bValue)
                cfAnd.AddOperand(pp.Negate());
            else
                cfAnd.AddOperand(pp);

            pa.Preconditions = cfAnd;

            cfAnd = new CompoundFormula("and");
            cfAnd.AddOperand(new PredicateFormula(pKNotT));
            pa.SetEffects( cfAnd);
            return pa;
        }


        private Action GenerateAssertInvalid(ParametrizedPredicate pp, Formula fGoal)
        {
            string sName = "AssertInvalid";
            sName += "_" + pp.Name;
            ParametrizedAction pa = new ParametrizedAction(sName);
            Parameter pTag = new Parameter(TAG, TAG_PARAMETER);
            foreach (Parameter param in pp.Parameters)
                pa.AddParameter(param);
            pa.AddParameter(pTag);
            CompoundFormula cfAnd = new CompoundFormula("and");
            ParametrizedPredicate ppKGivenT = new ParametrizedPredicate("KGiven" + pp.Name);
            foreach (Parameter param in pp.Parameters)
                ppKGivenT.AddParameter(param);
            ppKGivenT.AddParameter(pTag);
            ppKGivenT.AddParameter(new Parameter(Domain.VALUE, Domain.TRUE_VALUE));
            cfAnd.AddOperand(ppKGivenT);

            ppKGivenT = new ParametrizedPredicate("KGiven" + pp.Name);
            foreach (Parameter param in pp.Parameters)
                ppKGivenT.AddParameter(param);
            ppKGivenT.AddParameter(pTag);
            ppKGivenT.AddParameter(new Parameter(Domain.VALUE, Domain.FALSE_VALUE));
            cfAnd.AddOperand(ppKGivenT);

            pa.Preconditions = cfAnd;

            cfAnd = new CompoundFormula("and");
            cfAnd.AddOperand(fGoal);

            HashSet<Predicate> lAllGoal = fGoal.GetAllPredicates();
            foreach (Predicate p in lAllGoal)
            {
                if(!AlwaysKnown(p))
                    cfAnd.AddOperand(new KnowPredicate(p));
            } 

            pa.SetEffects( cfAnd);
            return pa;
        }


        private List<Action> GenerateRefutationActions(ParametrizedPredicate pp, Dictionary<string, List<Predicate>> dTags)
        {
            List<Action> lRefutations = new List<Action>();
            foreach (string sTag in dTags.Keys)
            {
                ParametrizedAction pa = new ParametrizedAction("Refute-" + pp.Name);
                foreach (Parameter param in pp.Parameters)
                    pa.AddParameter(param);
                CompoundFormula cfAnd = new CompoundFormula("and");
                ParametrizedPredicate ppKGivenT = new ParametrizedPredicate("K" + pp.Name + "_" + sTag);
                GroundedPredicate pKNotT = new GroundedPredicate("KNot");
                pKNotT.AddConstant(new Constant(TAG, sTag));
                foreach (Parameter param in pp.Parameters)
                    ppKGivenT.AddParameter(param);
                cfAnd.AddOperand(new PredicateFormula(ppKGivenT));
                cfAnd.AddOperand(pp.Negate());
                pa.Preconditions = cfAnd;
                cfAnd = new CompoundFormula("and");
                cfAnd.AddOperand(new PredicateFormula(pKNotT));
                pa.SetEffects(cfAnd);
                lRefutations.Add(pa);
            }
            return lRefutations;
        }

        private void WriteKnowledgeActions(StreamWriter sw)
        {
            foreach (Action a in Actions)
            {
                if (!a.HasConditionalEffects)
                    WriteKnowledgeAction(sw, a);
                else
                {
                    Action aKnowledge = a.AddKnowledgeConditions(m_lAlwaysKnown);
                    WriteConditionalAction(sw, aKnowledge);
                }
            }
        }

        private void RemoveConflictingConditionalEffectsFromAction(Action a)
        {
            CompoundFormula cfPreconditions = null;
            if (a.Preconditions == null)
            {
                cfPreconditions = new CompoundFormula("and");
                a.Preconditions = cfPreconditions;
            }
            else if (a.Preconditions is PredicateFormula)
            {
                cfPreconditions = new CompoundFormula("and");
                cfPreconditions.AddOperand(a.Preconditions);
                a.Preconditions = cfPreconditions;
            }
            else
            {
                cfPreconditions = (CompoundFormula)a.Preconditions;
            }
            cfPreconditions.AddOperand(new GroundedPredicate("axioms-applied"));

            CompoundFormula cfEffects = new CompoundFormula("and");
            cfEffects.AddOperand(new GroundedPredicate("axioms-applied").Negate());
            if (a.Effects is PredicateFormula)
            {
                cfEffects.AddOperand(a.Effects);
                a.SetEffects( cfEffects);
            }
            else
            {
                CompoundFormula cfOldEffects = (CompoundFormula)a.Effects;
                foreach (Formula f in cfOldEffects.Operands)
                {
                    if (f is PredicateFormula)
                        cfEffects.AddOperand(f);
                    else
                        cfEffects.AddOperand(((CompoundFormula)f).ReplaceNegativeEffectsInCondition());

                }
            }
            a.SetEffects( cfEffects);
        }

        private void WriteConditionalAction(StreamWriter sw, Action aKnowledge)
        {
            sw.WriteLine("(:action " + aKnowledge.Name);
            if (aKnowledge is ParametrizedAction)
            {
                ParametrizedAction pa = (ParametrizedAction)aKnowledge;
                sw.Write(":parameters (");
                foreach (Parameter param in pa.Parameters)
                    sw.Write(" " + param.Name + " - " + param.Type);
                sw.WriteLine(")");
            }
            if (RemoveConflictingConditionalEffects)
            {
                RemoveConflictingConditionalEffectsFromAction(aKnowledge);
            }


            if (aKnowledge.Preconditions != null)
                sw.WriteLine(":precondition " + aKnowledge.Preconditions);
            sw.WriteLine(":effect " + aKnowledge.Effects.ToString().Replace("(when", "\n\t(when"));
            sw.WriteLine(")");
        }
        /* using KW predicates
        private void WriteTaggedPredicatesNoState(StreamWriter sw, List<Predicate> lAdditinalPredicates)
        {
            sw.WriteLine("(:predicates");
            foreach (ParametrizedPredicate pp in Predicates)
            {
                /*
                if (pp.Name != Domain.OPTION_PREDICATE)
                {
                    sw.Write("(K" + pp.Name);//write know predicate
                    foreach (Parameter p in pp.Parameters)
                        sw.Write(" " + p.FullString());
                    sw.Write(" " + VALUE_PARAMETER + " - " + VALUE);
                    sw.WriteLine(")");
                }
                 * *
                if (AlwaysConstant(pp) && AlwaysKnown(pp))
                {
                    sw.Write("(K" + pp.Name);//write know predicate
                    foreach (Parameter p in pp.Parameters)
                        sw.Write(" " + p.FullString());
                    sw.Write(" " + VALUE_PARAMETER + " - " + VALUE);
                    sw.WriteLine(")");
                }
                if (!AlwaysConstant(pp) || !AlwaysKnown(pp))
                {
                    /*
                    sw.Write("(KGiven" + pp.Name);//write know-given predicate
                    foreach (Parameter p in pp.Parameters)
                        sw.Write(" " + p.FullString());
                    sw.Write(" " + TAG_PARAMETER + " - " + TAG);
                    sw.Write(" " + VALUE_PARAMETER + " - " + VALUE);
                    sw.WriteLine(")");
                     * *
                    sw.Write("(Given" + pp.Name);//write given predicate
                    foreach (Parameter p in pp.Parameters)
                        sw.Write(" " + p.FullString());
                    sw.Write(" " + TAG_PARAMETER + " - " + TAG);
                    sw.WriteLine(")");
                }
                if (!AlwaysKnown(pp) && pp.Name != Domain.OPTION_PREDICATE)
                {
                    /*
                    sw.Write("(KW" + pp.Name);//write know-whether predicate
                    foreach (Parameter p in pp.Parameters)
                        sw.Write(" " + p.FullString());
                    sw.WriteLine(")");
                    *
                    //maybe we can further remove this for constant predicates? Not sure.
                    sw.Write("(KWGiven" + pp.Name);//write know-whether-given predicate
                    foreach (Parameter p in pp.Parameters)
                        sw.Write(" " + p.FullString());
                    sw.Write(" " + TAG_PARAMETER + " - " + TAG);
                    sw.WriteLine(")");
                }
            }

            sw.WriteLine("(KNot " + TAG_PARAMETER + "1 - " + TAG + " " + TAG_PARAMETER + "2 - " + TAG + ")");//for tag refutation

            for (int iTime = 0; iTime < TIME_STEPS; iTime++)
                sw.WriteLine("(time" + iTime + ")");

            if (lAdditinalPredicates != null)
            {
                foreach (Predicate p in lAdditinalPredicates)
                    sw.WriteLine(p);
            }
            sw.WriteLine(")");
        }
*/

        private void WriteTaggedPredicatesNoState(StreamWriter sw, List<Predicate> lAdditinalPredicates)
        {
            sw.WriteLine("(:predicates");
            if(lAdditinalPredicates == null)
                sw.WriteLine("(NotInAction)");
            foreach (ParametrizedPredicate pp in Predicates)
            {
                if (AlwaysConstant(pp) && AlwaysKnown(pp))
                {
                    sw.Write("(" + pp.Name);//write know predicate
                    foreach (Parameter p in pp.Parameters)
                        sw.Write(" " + p.FullString());
                    sw.WriteLine(")");
                }
                if (!AlwaysConstant(pp) || !AlwaysKnown(pp))
                {
                    sw.Write("(Given" + pp.Name);//write given predicate
                    foreach (Parameter p in pp.Parameters)
                        sw.Write(" " + p.FullString());
                    sw.Write(" " + TAG_PARAMETER + " - " + TAG);
                    sw.WriteLine(")");
                    if (SDRPlanner.SplitConditionalEffects)
                    {
                        sw.Write("(Given" + pp.Name + "-Add");//write givenp-add predicate
                        foreach (Parameter p in pp.Parameters)
                            sw.Write(" " + p.FullString());
                        sw.Write(" " + TAG_PARAMETER + " - " + TAG);
                        sw.WriteLine(")");
                        sw.Write("(Given" + pp.Name + "-Remove");//write givenp-remove predicate
                        foreach (Parameter p in pp.Parameters)
                            sw.Write(" " + p.FullString());
                        sw.Write(" " + TAG_PARAMETER + " - " + TAG);
                        sw.WriteLine(")");
                    }
                }
            }

            sw.WriteLine("(KNot " + TAG_PARAMETER + "1 - " + TAG + " " + TAG_PARAMETER + "2 - " + TAG + ")");//for tag refutation

            for (int iTime = 0; iTime < TIME_STEPS; iTime++)
                sw.WriteLine("(time" + iTime + ")");

            if (lAdditinalPredicates != null)
            {
                foreach (Predicate p in lAdditinalPredicates)
                    sw.WriteLine(p);
            }
            sw.WriteLine(")");
        }


        private void WriteTaggedPredicates(StreamWriter sw, List<Predicate> lAdditinalPredicates)
        {
            sw.WriteLine("(:predicates");
            foreach (ParametrizedPredicate pp in Predicates)
            {
                sw.Write("(" + pp.Name);//write regular predicate
                foreach (Parameter p in pp.Parameters)
                    sw.Write(" " + p.FullString());
                sw.WriteLine(")");


                if (RemoveConflictingConditionalEffects)
                {
                    sw.Write("(Not-" + pp.Name);//write regular predicate
                    foreach (Parameter p in pp.Parameters)
                        sw.Write(" " + p.FullString());
                    sw.WriteLine(")");
                }

                if (SDRPlanner.SplitConditionalEffects)
                {
                    sw.Write("(" + pp.Name + "-Add");//write regular predicate
                    foreach (Parameter p in pp.Parameters)
                        sw.Write(" " + p.FullString());
                    sw.WriteLine(")");
                    sw.Write("(" + pp.Name + "-Remove");//write regular predicate
                    foreach (Parameter p in pp.Parameters)
                        sw.Write(" " + p.FullString());
                    sw.WriteLine(")");
                }

                if (!AlwaysKnown(pp))
                {
                    sw.Write("(K" + pp.Name);//write know predicate
                    foreach (Parameter p in pp.Parameters)
                        sw.Write(" " + p.FullString());
                    sw.Write(" " + VALUE_PARAMETER + " - " + VALUE);
                    sw.WriteLine(")");

                    if (RemoveConflictingConditionalEffects)
                    {
                        sw.Write("(Not-K" + pp.Name);//write regular predicate
                        foreach (Parameter p in pp.Parameters)
                            sw.Write(" " + p.FullString());
                        sw.Write(" " + VALUE_PARAMETER + " - " + VALUE);
                        sw.WriteLine(")");
                    }

                    if (SDRPlanner.SplitConditionalEffects)
                    {
                        sw.Write("(K" + pp.Name + "-Add");//write know predicate
                        foreach (Parameter p in pp.Parameters)
                            sw.Write(" " + p.FullString());
                        sw.Write(" " + VALUE_PARAMETER + " - " + VALUE);
                        sw.WriteLine(")");
                        sw.Write("(K" + pp.Name + "-Remove");//write know predicate
                        foreach (Parameter p in pp.Parameters)
                            sw.Write(" " + p.FullString());
                        sw.Write(" " + VALUE_PARAMETER + " - " + VALUE);
                        sw.WriteLine(")");
                    }

                    sw.Write("(KGiven" + pp.Name);//write know-given predicate
                    foreach (Parameter p in pp.Parameters)
                        sw.Write(" " + p.FullString());
                    sw.Write(" " + TAG_PARAMETER + " - " + TAG);
                    sw.Write(" " + VALUE_PARAMETER + " - " + VALUE);
                    sw.WriteLine(")");

                    if (RemoveConflictingConditionalEffects)
                    {
                        sw.Write("(Not-KGiven" + pp.Name);//write regular predicate
                        foreach (Parameter p in pp.Parameters)
                            sw.Write(" " + p.FullString());
                        sw.Write(" " + TAG_PARAMETER + " - " + TAG);
                        sw.Write(" " + VALUE_PARAMETER + " - " + VALUE);
                        sw.WriteLine(")");
                    }

                    if (SDRPlanner.SplitConditionalEffects)
                    {
                        sw.Write("(KGiven" + pp.Name + "-Add");//write know-given predicate
                        foreach (Parameter p in pp.Parameters)
                            sw.Write(" " + p.FullString());
                        sw.Write(" " + TAG_PARAMETER + " - " + TAG);
                        sw.Write(" " + VALUE_PARAMETER + " - " + VALUE);
                        sw.WriteLine(")");
                        sw.Write("(KGiven" + pp.Name + "-Remove");//write know-given predicate
                        foreach (Parameter p in pp.Parameters)
                            sw.Write(" " + p.FullString());
                        sw.Write(" " + TAG_PARAMETER + " - " + TAG);
                        sw.Write(" " + VALUE_PARAMETER + " - " + VALUE);
                        sw.WriteLine(")");
                    }
                }
            }
            sw.WriteLine("(KNot " + TAG_PARAMETER + " - " + TAG + ")");//for tag refutation

            if (RemoveConflictingConditionalEffects)
            {
                sw.WriteLine("(axioms-applied)");
                HashSet<GroundedPredicate> lGrounded = GroundAllPredicates();
                foreach (GroundedPredicate gp in lGrounded)
                {
                    sw.Write("(axioms-applied-" + gp.Name);
                    foreach (Constant c in gp.Constants)
                        sw.Write("-" + c.Name);
                    sw.WriteLine(")");
                }

            }
            /*
            if (m_bUseOptions)
            {
                sw.WriteLine("(option ?x - " + OPTION + ")");
            }
            */
            for (int iTime = 0; iTime < TIME_STEPS; iTime++)
                sw.WriteLine("(time" + iTime + ")");

            if (lAdditinalPredicates != null)
            {
                foreach (Predicate p in lAdditinalPredicates)
                    sw.WriteLine(p);
            }
            sw.WriteLine(")");
        }

        private void WriteKnowledgePredicates(StreamWriter sw)
        {
            sw.WriteLine("(:predicates");
            foreach (ParametrizedPredicate pp in Predicates)
            {
                sw.Write("(" + pp.Name);//write regular predicate
                foreach (Parameter p in pp.Parameters)
                    sw.Write(" " + p.FullString());
                sw.WriteLine(")");
                sw.Write("(K" + pp.Name);//write know predicate
                foreach (Parameter p in pp.Parameters)
                    sw.Write(" " + p.FullString());
                sw.WriteLine(")");
            }
            sw.WriteLine(")");
        }

        private void WriteConstants(StreamWriter sw)
        {
            sw.WriteLine("(:constants");
            foreach (Constant c in Constants)
                sw.WriteLine(" " + c.FullString());
            sw.WriteLine(")");
        }

        private void WriteConstants(StreamWriter sw, Dictionary<string, List<Predicate>> dTags)
        {
            sw.WriteLine("(:constants");
            foreach (Constant c in Constants)
                sw.WriteLine(" " + c.FullString());
            foreach (KeyValuePair<string, List<Predicate>> p in dTags)
            {
                sw.Write(" " + p.Key + " - " + TAG + " ;");
                foreach (Predicate pred in p.Value)
                {
                    sw.Write(" " + pred.ToString());
                }
                sw.WriteLine();
            }
            sw.WriteLine(" " + TRUE_VALUE + " - " + VALUE);
            sw.WriteLine(" " + FALSE_VALUE + " - " + VALUE);
            /*
            if (m_bUseOptions && HasNonDeterministicActions())
            {
                int cOptions = MaxNonDeterministicEffects();
                for( int i = 0 ; i < cOptions ; i++ )
                    sw.Write(" " + "opt" + i + " - " + OPTION);
                sw.WriteLine();
            }
             * */
            sw.WriteLine(")");
        }

        private void WriteTypes(StreamWriter sw, bool bUseTags)
        {
            sw.Write("(:types");
            foreach (string sType in Types)
                sw.Write(" " + sType);
            if (bUseTags)
            {
                sw.Write(" " + TAG);
                sw.Write(" " + VALUE);
            }
            /*
            if (m_bUseOptions && HasNonDeterministicActions())
            {
                sw.Write(" " + OPTION);
            }
             * */
            sw.WriteLine(")");
        }

        public bool HasNonDeterministicActions()
        {
            foreach (Action a in Actions)
            {
                if (a.ContainsNonDeterministicEffect)
                    return true;
            }
            return false;
        }

        public int MaxNonDeterministicEffects()
        {
            int cMaxOptions = 0;
            foreach (Action a in Actions)
            {
                if (a.ContainsNonDeterministicEffect)
                {
                    if (a.Effects.GetMaxNonDeterministicOptions() > cMaxOptions)
                        cMaxOptions = a.Effects.GetMaxNonDeterministicOptions();
                }
            }
            return cMaxOptions;
        }

        private Action GetActionByName(string sActionName)
        {
            foreach (Action a in Actions)
            {
                if (a.Name.ToLower() == sActionName.ToLower())
                {
                    return a;
                }
                if (a.Name.ToLower().Replace("_", "-") == sActionName)
                    return a;
            }
            Action aBestMatch = null;
            foreach (Action a in Actions)
            {
                if (sActionName.StartsWith(a.Name.ToLower())) //assuming that this is a splitted conditional effect action. BUGBUG - need better solution for this
                {
                    if (aBestMatch == null || aBestMatch.Name.Length < a.Name.Length)
                        aBestMatch = a;
                }
                if (sActionName.StartsWith(a.Name.ToLower().Replace("_", "-"))) //assuming that this is a splitted conditional effect action. BUGBUG - need better solution for this
                {
                    if (aBestMatch == null || aBestMatch.Name.Length < a.Name.Length)
                        aBestMatch = a;
                }
            }
            return aBestMatch;
        }
        private Dictionary<string, Constant> GetBindings(ParametrizedAction pa, string[] asAction)
        {
            if (pa.Parameters.Count > asAction.Length - 1)//last parameter can be the tag of a KW action
                return null;
            Dictionary<string, Constant> dBindings = new Dictionary<string, Constant>();
            for (int iParameter = 0; iParameter < pa.Parameters.Count; iParameter++)
            {
                dBindings[pa.Parameters[iParameter].Name] = new Constant(pa.Parameters[iParameter].Type, asAction[iParameter + 1]);
            }
            return dBindings;
        }
        public Action GroundActionByName(string[] asAction, IEnumerable<Predicate> lPredicates, bool bContainsNegations)
        {
            string sActionName = asAction[0];
            Action a = GetActionByName(sActionName);
            if(!(a is ParametrizedAction))
                return a;
            ParametrizedAction pa = (ParametrizedAction)a;                       
            Dictionary<string, Constant> dBindings = GetBindings(pa, asAction);

            Formula fGroundedPreconditions = null;
            if(pa.Preconditions != null)
                fGroundedPreconditions = pa.Preconditions.Ground(dBindings);
            if (pa.Preconditions == null || fGroundedPreconditions.ContainedIn(lPredicates, bContainsNegations))
            {
                string sName = pa.Name;
                foreach (Parameter p in pa.Parameters)
                    sName += "_" + dBindings[p.Name].Name;
                Action aGrounded = new Action(sName);
                aGrounded.Preconditions = fGroundedPreconditions;
                if (pa.Effects != null)
                    aGrounded.SetEffects( pa.Effects.Ground(dBindings));
                if (pa.Observe != null)
                    aGrounded.Observe = pa.Observe.Ground(dBindings);
                return aGrounded;
            }
            return null;
        }

        public Action GroundActionByName(string[] asAction)
        {
            string sActionName = asAction[0];
            Action a = GetActionByName(sActionName);
            if (!(a is ParametrizedAction))
                return a;
            ParametrizedAction pa = (ParametrizedAction)a;
            Dictionary<string, Constant> dBindings = GetBindings(pa, asAction);

            Formula fGroundedPreconditions = null;
            if (pa.Preconditions != null)
                fGroundedPreconditions = pa.Preconditions.Ground(dBindings);
            else if (pa.Effects != null)
                pa.Effects.Ground(dBindings);
            else if (pa.Observe != null)
                pa.Observe.Ground(dBindings);
            string sName = pa.Name;
            foreach (Parameter p in pa.Parameters)
                sName += "_" + dBindings[p.Name].Name;
            Action aGrounded = new Action(sName);
            aGrounded.Preconditions = fGroundedPreconditions;
            if (pa.Effects != null)
                aGrounded.SetEffects( pa.Effects.Ground(dBindings));
            if (pa.Observe != null)
                aGrounded.Observe = pa.Observe.Ground(dBindings);
            return aGrounded;
        }

        public void GroundPredicate(ParametrizedPredicate pp, Dictionary<Parameter, Constant> dBindings, List<Argument> lRemaining, HashSet<GroundedPredicate> lGrounded)
        {
            if (lRemaining.Count == 0)
            {
                GroundedPredicate gp = new GroundedPredicate(pp.Name);
                foreach (Parameter p in pp.Parameters)
                    gp.AddConstant(dBindings[p]);
                lGrounded.Add(gp);
            }
            else
            {
                Argument a = lRemaining[0];
                List<Argument> lNewRemaining = new List<Argument>(lRemaining);
                lNewRemaining.RemoveAt(0);
                if (a is Parameter)
                {
                    Parameter p = (Parameter)a;
                    foreach (Constant c in Constants)
                    {
                        if (p.Type == "" || c.Type == p.Type)
                        {
                            dBindings[p] = c;
                            GroundPredicate(pp, dBindings, lNewRemaining, lGrounded);
                        }
                    }
                }
                else
                {
                    GroundPredicate(pp, dBindings, lNewRemaining, lGrounded);
                }
            }
        }
        public HashSet<GroundedPredicate> GroundAllPredicates()
        {
            HashSet<string> lExcludePredicateNames = new HashSet<string>();
            return GroundAllPredicates(lExcludePredicateNames);
        }
        public HashSet<GroundedPredicate> GroundAllPredicates(HashSet<string> lExcludePredicateNames)
        {
            HashSet<GroundedPredicate> lGrounded = new HashSet<GroundedPredicate>();
            foreach (Predicate p in Predicates)
            {
                if (!lExcludePredicateNames.Contains(p.Name))
                {
                    if (p is ParametrizedPredicate)
                    {
                        ParametrizedPredicate pp = (ParametrizedPredicate)p;
                        GroundPredicate(pp, new Dictionary<Parameter, Constant>(),
                            new List<Argument>(pp.Parameters), lGrounded);
                    }
                    else
                        lGrounded.Add((GroundedPredicate)p);
                }
            }
            return lGrounded;
        }

        public List<Action> GroundAllActions(List<Action> lActions, IEnumerable<Predicate> lPredicates, bool bContainsNegations, bool bCheckConsistency)
        {
            List<Action> lGrounded = new List<Action>();
            Dictionary<string, Constant> dBindings = new Dictionary<string, Constant>();
            List<Parameter> lToBind = null;
            List<Constant> lConstants = new List<Constant>();
            foreach (Predicate p in lPredicates)
            {
                if (p is GroundedPredicate)
                {
                    GroundedPredicate gp = (GroundedPredicate)p;
                    foreach (Constant c in gp.Constants)
                        if (!lConstants.Contains(c))
                            lConstants.Add(c);
                }

            }
            foreach (Action a in lActions)
            {
                if (a is ParametrizedAction)
                {
                    ParametrizedAction pa = (ParametrizedAction)a;
                    lToBind = new List<Parameter>(pa.Parameters);
                    dBindings.Clear();
                    //GroundAction(pa, lConstants, lToBind, dBindings, lGrounded, lPredicates, bContainsNegations, bCheckConsistency);
                    GroundAction(pa, lConstants, lToBind, lGrounded, lPredicates, bContainsNegations, bCheckConsistency);
                }
                else
                {
                    if (a.Preconditions == null || !bCheckConsistency || a.Preconditions.IsTrue(lPredicates, bContainsNegations))
                        lGrounded.Add(a);
                }
            }
            return lGrounded;
        }
        public List<Action> GroundAllActions(IEnumerable<Predicate> lPredicates, bool bContainsNegations)
        {
            return GroundAllActions(Actions, lPredicates, bContainsNegations, true);
        }

        public List<Action> GroundAllActions()
        {
            List<Action> lGrounded = new List<Action>();
            Dictionary<string, Constant> dBindings = new Dictionary<string, Constant>();
            List<Parameter> lToBind = null;
            List<Constant> lConstants = new List<Constant>();
            
            foreach (Action a in Actions)
            {
                if (a is ParametrizedAction)
                {
                    ParametrizedAction pa = (ParametrizedAction)a;
                    lToBind = new List<Parameter>(pa.Parameters);
                    dBindings.Clear();
                    GroundAction(pa, lToBind, dBindings, lGrounded);
                }
                else
                {
                    lGrounded.Add(a);
                }
            }
            return lGrounded;
        }

        public List<Action> GroundAllObservationActions(IEnumerable<Predicate> lPredicates, bool bContainsNegations)
        {
            List<Action> lGrounded = new List<Action>();
            Dictionary<string, Constant> dBindings = new Dictionary<string, Constant>();
            HashSet<Predicate> lToBind = null;
            //List<Constant> lConstants = new List<Constant>();
            /* can't use these because the observations do not appear in the preconditions
            foreach (Predicate p in lPredicates)
            {
                if (p is GroundedPredicate)
                {
                    GroundedPredicate gp = (GroundedPredicate)p;
                    foreach (Constant c in gp.Constants)
                        if (!lConstants.Contains(c))
                            lConstants.Add(c);
                }
            }
             * */
            foreach (Action a in Actions)
            {
                if (a.Observe != null)
                {
                    if (a is ParametrizedAction)
                    {
                        /*
                        ParametrizedAction pa = (ParametrizedAction)a;
                        lToBind = new List<Parameter>(pa.Parameters);
                        dBindings.Clear();
                        GroundAction(pa, Constants, lToBind, dBindings, lGrounded, lPredicates, bContainsNegations, true);
                         */
                        ParametrizedAction pa = (ParametrizedAction)a;
                        lToBind = new HashSet<Predicate>();
                        if (pa.Preconditions != null)
                            pa.Preconditions.GetAllPredicates(lToBind);
                        dBindings.Clear();
                        GroundAction(pa, Constants, new List<Predicate>(lToBind), dBindings, lGrounded, lPredicates, bContainsNegations, true);

                    }
                    else
                        lGrounded.Add(a);
                }
            }
            List<Action> lFilteredKnown = new List<Action>();
            foreach (Action a in lGrounded)
            {
                PredicateFormula pf = (PredicateFormula)a.Observe;
                if (!lPredicates.Contains(pf.Predicate) &&
                    !lPredicates.Contains(pf.Predicate.Negate()))
                    lFilteredKnown.Add(a);
            }
            return lFilteredKnown;
        }

        private void GroundAction(ParametrizedAction pa, List<Constant> lConstants,
            List<Parameter> lToBind, Dictionary<string, Constant> dBindings,
            List<Action> lGrounded, IEnumerable<Predicate> lPredicates, bool bContainsNegations, bool bCheckConsistency)
        {
            Formula fGroundedPreconditions = null;
            if (lToBind.Count > 0)
            {
                Parameter p = lToBind.First();
                lToBind.Remove(p);
                foreach (Constant c in lConstants)
                {
                    if (c.Type == p.Type)
                    {
                        dBindings[p.Name] = c;

                        if (pa.Preconditions != null)
                            fGroundedPreconditions = pa.Preconditions.PartiallyGround(dBindings);
                        if (pa.Preconditions == null || !bCheckConsistency || !fGroundedPreconditions.IsFalse(lPredicates, bContainsNegations))
                            GroundAction(pa, lConstants, lToBind, dBindings, lGrounded, lPredicates, bContainsNegations, bCheckConsistency);
                        else
                            Debug.Assert(false);
                    }
                }
                dBindings.Remove(p.Name);
                lToBind.Add(p);
            }
            else
            {
                if(pa.Preconditions != null)
                    fGroundedPreconditions = pa.Preconditions.Ground(dBindings);
                if (pa.Preconditions == null || !bCheckConsistency || fGroundedPreconditions.ContainedIn(lPredicates, bContainsNegations))
                {
                    string sName = pa.Name;
                    foreach (Parameter p in pa.Parameters)
                        sName += "_" + dBindings[p.Name].Name;
                    Action aGrounded = new Action(sName);
                    aGrounded.Preconditions = fGroundedPreconditions;
                    if (pa.Effects != null)
                        aGrounded.SetEffects( pa.Effects.Ground(dBindings));
                    if (pa.Observe != null)
                        aGrounded.Observe = pa.Observe.Ground(dBindings);
                    if((pa.Preconditions == null || !aGrounded.Preconditions.IsFalse(new List<Predicate>()) )&&
                        (aGrounded.Effects == null || !aGrounded.Effects.IsFalse(new List<Predicate>())))
                        lGrounded.Add(aGrounded);
                }
            }
        }

        private void GroundAction(ParametrizedAction pa, List<Constant> lConstants,
            List<Parameter> lToBind,
            List<Action> lGrounded, IEnumerable<Predicate> lPredicates, bool bContainsNegations, bool bCheckConsistency)
        {
            Formula fGroundedPreconditions = null;
            List<Predicate> lPre = new List<Predicate>();
            if (pa.Preconditions != null)
                lPre = new List<Predicate>(pa.Preconditions.GetAllPredicates());
            List<Dictionary<string, Constant>> lBindings = FindValidBindings(lToBind, lPre, lPredicates, bContainsNegations);
            foreach (var dBindings in lBindings) 
            {
                if (pa.Preconditions != null)
                    fGroundedPreconditions = pa.Preconditions.Ground(dBindings);
                if (pa.Preconditions == null || !bCheckConsistency || fGroundedPreconditions.ContainedIn(lPredicates, bContainsNegations))
                {
                    string sName = pa.Name;
                    foreach (Parameter p in pa.Parameters)
                        sName += "_" + dBindings[p.Name].Name;
                    Action aGrounded = new Action(sName);
                    aGrounded.Preconditions = fGroundedPreconditions;
                    if (pa.Effects != null)
                        aGrounded.SetEffects(pa.Effects.Ground(dBindings));
                    if (pa.Observe != null)
                        aGrounded.Observe = pa.Observe.Ground(dBindings);
                    if ((pa.Preconditions == null || !aGrounded.Preconditions.IsFalse(new List<Predicate>())) &&
                        (aGrounded.Effects == null || !aGrounded.Effects.IsFalse(new List<Predicate>())))
                        lGrounded.Add(aGrounded);
                }
            }
        }



        private void FindValidBindings(List<Parameter> lToBind, List<Dictionary<string, Constant>> lBindings, Dictionary<string, Constant> dBinding, bool bContainsNegations)
        {
            if (lToBind.Count == 0 )
            {
                lBindings.Add(dBinding);
                return;
            }

            Parameter pFirst = lToBind[0];
            List<Parameter> lNewToBind = new List<Parameter>(lToBind);
            lNewToBind.RemoveAt(0);
            foreach (Constant c in Constants)
            {
                if (c.Type == pFirst.Type)
                {
                    Dictionary<string, Constant> dNewBinding = new Dictionary<string, Constant>(dBinding);
                    dNewBinding[pFirst.Name] = c;
                    FindValidBindings(lNewToBind, lBindings, dNewBinding, bContainsNegations);
                }
            }
        }



        private void FindValidBindings(List<Parameter> lToBind, List<Dictionary<string, Constant>> lBindings, Dictionary<string, Constant> dBinding,
            List<Predicate> lPreconditions, IEnumerable<Predicate> lPredicates, bool bContainsNegations)
        {
            if (lToBind.Count == 0 || lPreconditions.Count == 0)
            {
                if (lToBind.Count != 0)
                    FindValidBindings(lToBind, lBindings, dBinding, bContainsNegations);
                else
                    lBindings.Add(dBinding);
                return;
            }



            Predicate p = lPreconditions[0];
            List<Predicate> lReducedPreconditions = new List<Predicate>();
            for (int i = 1; i < lPreconditions.Count; i++)
                lReducedPreconditions.Add(lPreconditions[i]);

            if (p != null && p is ParametrizedPredicate && ((ParametrizedPredicate)p).Parameters.Count() > 0)
            {
                ParametrizedPredicate pCurrent = (ParametrizedPredicate)p;
                if (pCurrent.Negation && !bContainsNegations)
                    throw new NotImplementedException();


                List<GroundedPredicate> lMatches = new List<GroundedPredicate>();
                foreach (GroundedPredicate pGrounded in lPredicates)
                {
                    if (pCurrent.Name == pGrounded.Name && pCurrent.Negation == pGrounded.Negation)
                        lMatches.Add(pGrounded);
                }

                foreach (GroundedPredicate gpMatch in lMatches)
                {
                    Dictionary<string, Constant> dNewBinding = pCurrent.Match(gpMatch, dBinding);
                    if (dNewBinding != null)
                    {
                        foreach (var v in dBinding)
                            dNewBinding[v.Key] = v.Value;
                        List<Parameter> lNewToBind = new List<Parameter>();
                        foreach (Parameter param in lToBind)
                        {
                            bool bExists = false;
                            foreach (string s in dNewBinding.Keys)
                                if (param.Name == s)
                                    bExists = true;
                            if (!bExists)
                                lNewToBind.Add(param);
                        }
                        FindValidBindings(lNewToBind, lBindings, dNewBinding, lReducedPreconditions, lPredicates, bContainsNegations);
                    }

                }

            }
            else
            {
                FindValidBindings(lToBind, lBindings, dBinding, lReducedPreconditions, lPredicates, bContainsNegations);

            }


        }


        private List<Dictionary<string, Constant>> FindValidBindings(List<Parameter> lToBind, List<Predicate> lPreconditions, IEnumerable<Predicate> lPredicates, bool bContainsNegations)
        {
            List<Dictionary<string, Constant>> lBindings = new List<Dictionary<string, Constant>>();
            Dictionary<string, Constant> dBinding = new Dictionary<string, Constant>();

            Predicate pAt = null;
            for (int i = 0; i < lPreconditions.Count; i++)
            {
                if (lPreconditions[i].Name == "at")
                {
                    pAt = lPreconditions[i];
                    lPreconditions[i] = lPreconditions[0];
                    lPreconditions[0] = pAt;
                    break;
                }
            }
 
            FindValidBindings(lToBind, lBindings, dBinding, lPreconditions, lPredicates, bContainsNegations);
            return lBindings;
        }



        private void GroundAction(ParametrizedAction pa, List<Constant> lConstants,
            List<Predicate> lToBind, Dictionary<string, Constant> dBindings,
            List<Action> lGrounded, IEnumerable<Predicate> lPredicates, bool bContainsNegations, bool bCheckConsistency)
        {
            if (lToBind.Count > 0)
            {
                ParametrizedPredicate p = (ParametrizedPredicate)lToBind.First();
                lToBind.Remove(p);
                foreach (GroundedPredicate pExists in lPredicates)
                {
                    Dictionary<string, Constant> dNewBindings = p.Match(pExists, dBindings);
                    if (dNewBindings != null)
                    {
                        foreach (KeyValuePair<string, Constant> pair in dNewBindings)
                        {
                            dBindings[pair.Key] = pair.Value;
                        }
                        GroundAction(pa, lConstants, lToBind, dBindings, lGrounded, lPredicates, bContainsNegations, bCheckConsistency);
                        foreach (KeyValuePair<string, Constant> pair in dNewBindings)
                        {
                            dBindings.Remove(pair.Key);
                        }
                    }
                }
                lToBind.Add(p);
            }
            else
            {
                List<Parameter> lUnboundedParameters = new List<Parameter>();
                foreach (Parameter p in pa.Parameters)
                {
                    if (!dBindings.ContainsKey(p.Name))
                        lUnboundedParameters.Add(p);
                }
                GroundAction(pa, lConstants, lUnboundedParameters, dBindings, lGrounded, lPredicates, bContainsNegations, bCheckConsistency);
            }
                
        }



        private void GroundAction(ParametrizedAction pa,
            List<Parameter> lToBind, Dictionary<string, Constant> dBindings,
            List<Action> lGrounded)
        {
            if (lToBind.Count > 0)
            {
                Parameter p = lToBind.Last();
                lToBind.Remove(p);
                foreach (Constant c in Constants)
                {
                    if (c.Type == p.Type)
                    {
                        dBindings[p.Name] = c;
                        GroundAction(pa, lToBind, dBindings, lGrounded);
                    }
                }
                dBindings.Remove(p.Name);
                lToBind.Add(p);
            }
            else
            {
                Formula fGroundedPreconditions = null;
                if (pa.Preconditions != null)
                    fGroundedPreconditions = pa.Preconditions.Ground(dBindings);
                string sName = pa.Name;
                foreach (Parameter p in pa.Parameters)
                    sName += "_" + dBindings[p.Name].Name;
                Action aGrounded = new Action(sName);
                aGrounded.Preconditions = fGroundedPreconditions;
                if (pa.Effects != null)
                    aGrounded.SetEffects( pa.Effects.Ground(dBindings));
                if (pa.Observe != null)
                    aGrounded.Observe = pa.Observe.Ground(dBindings);
                lGrounded.Add(aGrounded);

            }
        }



        private Dictionary<string, string> m_dConstantNameToType;
        public Dictionary<string, string> ConstantNameToType {
            get
            {
                if (m_dConstantNameToType == null)
                {
                    m_dConstantNameToType = new Dictionary<string, string>();
                    foreach (Constant c in Constants)
                    {
                        m_dConstantNameToType[c.Name] = c.Type;
                    }
                }
                return m_dConstantNameToType;
            }
        }

        public bool AlwaysKnown(Predicate p)
        {
            return m_lAlwaysKnown.Contains(p.Name);
        }

        public bool Observable(Predicate p)
        {
            return m_lObservable.Contains(p.Name);
        }

        public bool AlwaysConstant(Predicate p)
        {
            return m_lAlwaysConstant.Contains(p.Name);
        }

        public void AddHidden(CompoundFormula cf)
        {
            HashSet<Predicate> lUnknown = new HashSet<Predicate>();
            cf.GetAllPredicates(lUnknown);
            foreach (Predicate p in lUnknown)
                m_lAlwaysKnown.Remove(p.Name);
        }

        public void ComputeAlwaysKnown()
        {
            bool bChanged = true;
            while (bChanged)
            {
                bChanged = false;
                foreach (Action a in Actions)
                {
                    if (a.HasConditionalEffects)
                    {
                        foreach (CompoundFormula cfCondition in a.GetConditions())
                        {
                            HashSet<Predicate> lIfPredicates = new HashSet<Predicate>();
                            cfCondition.Operands[0].GetAllPredicates(lIfPredicates);
                            bool bAllKnown = true;
                            foreach (Predicate p in lIfPredicates)
                            {
                                if (!m_lAlwaysKnown.Contains(p.Name))
                                    bAllKnown = false;
                            }
                            if (!bAllKnown)
                            {
                                HashSet<Predicate> lThenPredicates = new HashSet<Predicate>();
                                cfCondition.Operands[1].GetAllPredicates(lThenPredicates);
                                foreach (Predicate p in lThenPredicates)
                                {
                                    if (m_lAlwaysKnown.Contains(p.Name))
                                    {
                                        bChanged = true;
                                        m_lAlwaysKnown.Remove(p.Name);
                                    }
                                }
                            }
                        }
                    }
                    if (a.Observe != null)
                    {
                        HashSet<Predicate> lPredicates = a.Observe.GetAllPredicates();
                        foreach (Predicate p in lPredicates)
                        {
                            if (m_lAlwaysKnown.Contains(p.Name))
                            {
                                m_lAlwaysKnown.Remove(p.Name);
                            }
                        }
                    }
                }
            }
        }


        private void WritePredicates(StreamWriter sw)
        {
            sw.WriteLine("(:predicates");
            foreach (ParametrizedPredicate pp in Predicates)
            {
                sw.Write("(" + pp.Name);//write regular predicate
                foreach (Parameter p in pp.Parameters)
                    sw.Write(" " + p.FullString());
                sw.WriteLine(")");
            }
            sw.WriteLine(")");
        }
        private void WriteKReplannerActions(StreamWriter sw)
        {
            foreach (Action a in Actions)
            {
                if (a.Observe == null)
                    WriteAction(sw, a);
                else
                    WriteSensor(sw, a);
            }
        }

        public void WriteKReplannerDomain(string sFileName)
        {
            StreamWriter sw = new StreamWriter(sFileName);
            sw.WriteLine("(define (domain " + Name + ")");
            sw.WriteLine("(:requirements :strips :typing)");
            WriteTypes(sw, false);
            WriteConstants(sw);
            sw.WriteLine();
            WritePredicates(sw);
            sw.WriteLine();
            WriteKReplannerActions(sw);
            sw.WriteLine(")");
            sw.Close();
        }

        public void AddFunction(string sFunctionName)
        {
            Functions.Add(sFunctionName);
        }

        public bool IsFunctionExpression(string s)
        {
            s = s.ToLower();
            return s == "increase" || s == "decrease" || s == "=";
        }

        public CompoundFormula GetOptionsStatement()
        {
            CompoundFormula cfOneof = new CompoundFormula("oneof");
            int cOptions = Math.Max(MAX_OPTIONS, MaxNonDeterministicEffects());
            for (int iOption = 0; iOption < cOptions; iOption++)
            {
                GroundedPredicate gpCurrentOption = new GroundedPredicate(Domain.OPTION_PREDICATE);
                gpCurrentOption.AddConstant(new Constant(OPTION, "opt" + iOption));
                cfOneof.AddOperand(gpCurrentOption);
            }
            return cfOneof;

        }

        public bool IsObservationAction(string sActionName)
        {
            Action a = GetActionByName(sActionName);
            return a.Observe != null;
        }

        public void WriteSimpleDomain(string sFileName)
        {
            StreamWriter sw = new StreamWriter(sFileName);
            sw.WriteLine("(define (domain K" + Name + ")");
            sw.WriteLine("(:requirements :strips :typing)");
            WriteTypes(sw, false);
            WriteConstants(sw);
            sw.WriteLine();
            WritePredicates(sw);
            sw.WriteLine();
            WriteActions(sw, false);
            sw.WriteLine(")");
            sw.Close();
        }

        private void WriteActions(StreamWriter sw, bool bWriteObservationActions)
        {
            foreach (Action a in Actions)
            {
                if (bWriteObservationActions || a.Observe == null)
                    WriteAction(sw, a);
            }
        }

        public bool CompareTo(Domain d)
        {
            foreach (Action a in Actions)
            {
                bool bFound = false;
                foreach (Action aOther in d.Actions)
                {
                    if (a.Name == aOther.Name)
                    {
                        bFound = true;
                        if (!a.CompareTo(aOther))
                            return false;
                        break;
                    }
                }
                if (!bFound)
                    return false;
            }
            return true;
        }

        static bool CompareDomains(string sDomain1, string sDomain2)
        {
            Parser p = new Parser();
            Domain d1 = p.ParseDomain(sDomain1);
            Domain d2 = p.ParseDomain(sDomain2);
            return d1.CompareTo(d2);
        }

        public void RemoveUniversalQuantifiers(List<Predicate> lConstantPredicates)
        {
            List<Action> lFiltered = new List<Action>();
            foreach (Action a in Actions)
            {
                Action aFiltered = a.RemoveUniversalQuantifiers(Constants, lConstantPredicates, this);
                if (aFiltered != null)
                    lFiltered.Add(aFiltered);
                //a.SimplifyConditions();
            }
            Actions = lFiltered;
        }
    }
}
