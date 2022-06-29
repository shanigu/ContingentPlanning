using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Diagnostics;
using System.IO;

namespace PDDL
{
    public class PartiallySpecifiedState : DynamicBeliefState
    {
        public List<Action> AvailableActions { get; protected set; }
        public StaticBeliefState m_bsInitialBelief;

        public CompoundFormula m_cfCNFBelief;
        public static bool UseCFFBelief { get; set; }
        private List<Predicate> m_lFailureTag;
        private List<List<Predicate>> m_lPreviousTags;
        public List<string> History;


        public PartiallySpecifiedState(StaticBeliefState bs)
        {
            History = new List<string>();
            ID = STATE_COUNT++;
            Problem = bs.Problem;
            Predecessor = null;
            Known = new HashSet<Predicate>(bs.Observed);
            AvailableActions = new List<Action>();
            UnderlyingEnvironmentState = bs.UnderlyingEnvironmentState;
            m_bsInitialBelief = bs;
            CompoundFormula cfBelief = new CompoundFormula("and");
            Hidden = new HashSet<Predicate>();
            foreach (Formula f in bs.Hidden)
                foreach(Predicate p in f.GetAllPredicates())
                    Hidden.Add(p.Canonical());

            if (UseCFFBelief)
            {
                foreach (CompoundFormula cf in bs.Hidden)
                {
                    cfBelief.AddOperand(cf);
                    if (!SDRPlanner.OptimizeMemoryConsumption)
                    {
                        HashSet<Predicate> lCurrent = new HashSet<Predicate>();
                        cf.GetAllPredicates(lCurrent);
                        foreach (Predicate p in lCurrent)
                        {
                            if (p.Negation)
                            {
                                if (!Hidden.Contains(p.Negate()))
                                    Hidden.Add(p.Negate());
                            }
                            else if (!Hidden.Contains(p))
                                Hidden.Add(p);
                        }
                    }
                }
            }
            /* as long as there are no non-deterministic effects there is no need to maintain all knowledge
            foreach (Predicate p in bs.Observed)
            {
                if (!Problem.Domain.AlwaysKnown(p))
                    cfBelief.AddOperand(p);
            }
             * */
            if (UseCFFBelief)
            {
                cfBelief = (CompoundFormula)cfBelief.AddTime(0);
                m_cfCNFBelief = cfBelief.ToCNF();
                Time = 0;
            }

            FunctionValues = new Dictionary<string, double>();
            foreach (string sFunction in Problem.Domain.Functions)
            {
                FunctionValues[sFunction] = m_bsInitialBelief.FunctionValues[sFunction];
            }
        }
        public PartiallySpecifiedState(PartiallySpecifiedState sPredecessor, Action aGeneratingAction)
        {
            ID = STATE_COUNT++;

            History = new List<string>(sPredecessor.History);
            History.Add(aGeneratingAction.Name);

            m_bsInitialBelief = sPredecessor.m_bsInitialBelief;
            Problem = m_bsInitialBelief.Problem;
            AvailableActions = new List<Action>();
            UnderlyingEnvironmentState = null;
            Predecessor = sPredecessor;
            GeneratingAction = aGeneratingAction;
            if (SDRPlanner.OptimizeMemoryConsumption)
            {
                Known = new HashSet<Predicate>();
            }
            else
            {
                Hidden = new HashSet<Predicate>(sPredecessor.Hidden);
                Known = new HashSet<Predicate>(sPredecessor.Known);
                ForgetPotentialEffects();
            }
            FunctionValues = new Dictionary<string, double>();
            Time = sPredecessor.Time + 1;

            if (UseCFFBelief)
            {
                Hidden = new HashSet<Predicate>(sPredecessor.Hidden);
                m_cfCNFBelief = (CompoundFormula)sPredecessor.m_cfCNFBelief.Clone();
                CompoundFormula cfAction = GeneratingAction.ToTimeFormula(Time, Known, Hidden);
                if (cfAction != null)
                    m_cfCNFBelief.AddOperand(cfAction);
                if (m_cfCNFBelief.ToString().Contains("P_FALSE"))
                    Debug.WriteLine("BUGBUG");
            }

            foreach (KeyValuePair<string, double> p in sPredecessor.FunctionValues)
                FunctionValues[p.Key] = p.Value;
        }

        public override bool ConsistentWith(Predicate p, bool bCheckingActionPreconditions)
        {
            Predicate pNegate = p.Negate();
            if (Known.Contains(p))
                return true;
            if(Known.Contains(pNegate))
                return false;
            if(Predecessor == null)
                return m_bsInitialBelief.ConsistentWith(p, true);
            List<Formula> lRemovingPreconditions = new List<Formula>();
            foreach (CompoundFormula cfCondition in GeneratingAction.GetConditions())
            {
                HashSet<Predicate> lEffects = new HashSet<Predicate>();
                cfCondition.Operands[1].GetAllPredicates(lEffects);
                if (lEffects.Contains(p))
                {
                    if (Predecessor.ConsistentWith(cfCondition.Operands[0], bCheckingActionPreconditions))
                        return true;
                }
                /*
                if (lEffects.Contains(pNegate))
                {
                    //condition removes p
                    //if condition must have happened, then p cannot be true
                    //if the negation of the condition is not consistent, then the condition must have happened
                    //if the negation of the condition is not consistent, p cannot be true
                    Formula fNegate = cfCondition.Operands[0].Negate();
                    bool bCnsistent = Predecessor.ConsistentWith(fNegate);
                    if (!bCnsistent)
                        return false;
                }
                 */
                if (lEffects.Contains(pNegate))
                {
                    lRemovingPreconditions.Add(cfCondition.Operands[0]);
                }
            }
            if (lRemovingPreconditions.Count > 0)
            {
                //if one of the removing conditions must have happened, then p cannot be true
                //if the negation of (or f1 f2 ... fk) is not consistent, then one of f1 ... fk must be true
                //if (and ~f1 ... ~fk) is not consistent then one of f1 ... fk must be true
                //if (and ~f1 ... ~fk) is not consistent then p cannot be true
                CompoundFormula cfAnd = new CompoundFormula("and");
                foreach (Formula f in lRemovingPreconditions)
                    cfAnd.AddOperand(f.Negate());
                bool bConsistent = Predecessor.ConsistentWith(cfAnd, bCheckingActionPreconditions);
                if (!bConsistent)
                    return false;
            }
            return Predecessor.ConsistentWith(p, bCheckingActionPreconditions);
        }


        public override bool ConsistentWith(Formula fOriginal, bool bCheckingActionPreconditions)
        {
            PartiallySpecifiedState pssCurrent = this;
            Formula fCurrent = fOriginal;


            if (bCheckingActionPreconditions && SDRPlanner.ConsistentWithObservedOnly)
            {
                //We check the negation of the preconditions, so we should say that the negation may hold if we do not know that it doesn't
                if (fOriginal.IsFalse(pssCurrent.Known))
                    return false;
                return true;
            }


            if (UseCFFBelief)
            {
                Formula fReduced = fCurrent.Reduce(pssCurrent.Known);
                if (fReduced.IsTrue(null))
                    return true;
                if (fReduced.IsFalse(null))
                    return false;
                CompoundFormula cfCNF = (CompoundFormula)pssCurrent.m_cfCNFBelief.Clone();
                if (fReduced is PredicateFormula)
                {
                    cfCNF.AddOperand(new TimePredicate(((PredicateFormula)fReduced).Predicate, pssCurrent.Time));
                }
                else
                {
                    CompoundFormula cfTime = (CompoundFormula)fReduced.AddTime(pssCurrent.Time);
                    CompoundFormula cfTimeCNF = cfTime.ToCNF();
                    cfCNF.AddOperand(cfTimeCNF);
                }
                throw new NotImplementedException();
                List<List<Predicate>> lConsistentAssignments = null;// pssCurrent.m_bsInitialBelief.RunSatSolver(cfCNF, 1);
                if (lConsistentAssignments.Count == 0)
                {
                    return false;
                }
                if (bCheckingActionPreconditions)
                {
                    pssCurrent.m_bsInitialBelief.SetProblematicTag(lConsistentAssignments[0]);
                    pssCurrent.m_lFailureTag = lConsistentAssignments[0];
                }
                else if (pssCurrent.m_lFailureTag == null)
                {
                    pssCurrent.m_bsInitialBelief.SetProblematicTag(lConsistentAssignments[0]);
                    pssCurrent.m_lFailureTag = lConsistentAssignments[0];
                }
                return true;
            }
            else
            {
                Formula fReduced = null;
                int cRegressions = 0;
                while (pssCurrent.Predecessor != null)
                {
                    fReduced = fCurrent.Reduce(pssCurrent.Known);
                    if (fReduced.IsTrue(null))
                        return true;
                    if (fReduced.IsFalse(null))
                        return false;

                    Formula fToRegress = fReduced;
                    if (fToRegress is CompoundFormula)
                    {
                        //bool bChanged = false;
                        //fToRegress = ((CompoundFormula)fToRegress).RemoveNestedConjunction(out bChanged);
                    }
                    if (fToRegress.IsTrue(pssCurrent.Known))
                        return true;
                    if (fToRegress.IsFalse(pssCurrent.Known))
                        return false;
                    Formula fRegressed = fToRegress.Regress(pssCurrent.GeneratingAction, pssCurrent.Known);
                    //Formula fRegressed = fToRegress.Regress(GeneratingAction);
                    cRegressions++;

                    fCurrent = fRegressed;
                    pssCurrent = (PartiallySpecifiedState)pssCurrent.Predecessor;
                }
                fReduced = fCurrent.Reduce(pssCurrent.Known);
                if (fReduced.IsTrue(null))
                    return true;
                if (fReduced.IsFalse(null))
                    return false;
                return pssCurrent.m_bsInitialBelief.ConsistentWith(fReduced);
                //m_bsInitialBelief.ApplyReasoning();
            }
        }

        public override bool AddObserved(Predicate p)
        {

            if (p is ParametrizedPredicate)
                throw new NotImplementedException();
            if (p.Name == Domain.TRUE_PREDICATE)
                return false;

            if (UseCFFBelief && !Problem.Domain.AlwaysKnown(p) && !Known.Contains(p))
            {
                TimePredicate tp = new TimePredicate(p, Time);
                List<Predicate> lKnown = new List<Predicate>();
                lKnown.Add(tp);
                bool bChanged = true;
                CompoundFormula cfOriginal = (CompoundFormula)m_cfCNFBelief.Clone();
                CompoundFormula cfToReduce = m_cfCNFBelief;
                while (bChanged)
                {
                    bChanged = false;
                    CompoundFormula cfReduced = new CompoundFormula("and");
                    foreach (Formula fOperand in cfToReduce.Operands)
                    {
                        Formula fReduced = fOperand.Reduce(lKnown);
                        if (fReduced is CompoundFormula)
                        {
                            cfReduced.AddOperand(fReduced);
                        }
                        else
                        {
                            if (((PredicateFormula)fReduced).Predicate is TimePredicate)
                                lKnown.Add(((PredicateFormula)fReduced).Predicate);
                            bChanged = true;
                        }
                    }
                    cfToReduce = cfReduced;

                    /*
                    Formula fReduced = cfReduced.Reduce(lKnown);
                    if (fReduced is CompoundFormula)
                    {
                        cfReduced = (CompoundFormula)fReduced;
                        foreach (Formula fOpernad in cfReduced.Operands)
                        {
                            if (fOpernad is PredicateFormula)
                            {
                                PredicateFormula pf = (PredicateFormula)fOpernad;
                                lKnown.Add(pf.Predicate);
                                bChanged = true;
                            }
                        }
                        m_cfCNFBelief = cfReduced;
                    }
                    else
                    {
                        if (((PredicateFormula)fReduced).Predicate is TimePredicate)
                            lKnown.Add(((PredicateFormula)fReduced).Predicate);
                        m_cfCNFBelief = new CompoundFormula("and");
                        bChanged = false;
                    }*/
                }

                foreach (TimePredicate tpLearned in lKnown)
                {
                    if (tpLearned != tp)
                    {
                        if (tpLearned.Time == Time)
                            Debug.WriteLine("Learned " + tpLearned.Predicate);
                        AddToObservedList(tpLearned);
                    }
                }
                m_cfCNFBelief = cfToReduce;
                //m_cfCNFBelief.AddOperand(new TimePredicate(p, Time));
            }

            return AddToObservedList(p);
        }

        public override bool Equals(object obj)
        {
            if (obj is PartiallySpecifiedState)
            {
                PartiallySpecifiedState bs = (PartiallySpecifiedState)obj;
                if (bs.Known.Count != Known.Count)
                    return false;
                foreach (Predicate p in bs.Known)
                    if (!Known.Contains(p))
                        return false;
                return true;
            }
            return false;
        }

        public bool Contains(Formula f)
        {
            return f.ContainedIn(Known, true);
        }
        /*
        public virtual PartiallySpecifiedState Clone()
        {
            return new PartiallySpecifiedState(this);
        }
        */
        public bool IsApplicable(string sActionName)
        {
            Action a = Problem.Domain.GroundActionByName(sActionName.Split(' '));
            if (a == null)
                return false;
            return IsApplicable(a);
        }

        private bool IsApplicable(Action a)
        {
            if (a.Preconditions == null)
                return true;
            m_bsInitialBelief.MaintainProblematicTag = true;
            Formula fReduced = a.Preconditions.Reduce(Known);
            if (fReduced.IsTrue(Known))
                return true;
            if (fReduced.IsFalse(Known))
                return false;
            Formula fNegatePreconditions = fReduced.Negate();
            if (ConsistentWith(fNegatePreconditions, true))
            {
                return false;
            }
            AddObserved(a.Preconditions);
            return true;
        }

        public override DynamicBeliefState Apply(string sActionName, out Formula fObserve)
        {
            fObserve = null;
            Action a = Problem.Domain.GroundActionByName(sActionName.Split(' '));
            if (a == null)
                return null;
            DynamicBeliefState pssNext = Apply(a, out fObserve);
            return pssNext;
        }

        public override DynamicBeliefState Apply(Action a, out Formula fObserve)
        {
            return Apply(a, out fObserve, false);
        }

        public static TimeSpan tsPre = new TimeSpan(), tsEffects = new TimeSpan(), tsObs = new TimeSpan();

        private PartiallySpecifiedState Apply(Action aOrg, out Formula fObserve, bool bPropogateOnly)
        {
            //Debug.WriteLine("Executing " + a.Name);
            fObserve = null;
            if (aOrg is ParametrizedAction)
                return null;

            DateTime dtStart = DateTime.Now;

            Action a = aOrg.ApplyObserved(Known);

            //no need to check pre during propogation - they were already confirmed the first time
            if (!bPropogateOnly && a.Preconditions != null && !IsApplicable(a))
                return null;

            a.ComputeRegressions();

            tsPre += DateTime.Now - dtStart;
            dtStart = DateTime.Now;

            State sNew = null;
            if (!bPropogateOnly && UnderlyingEnvironmentState != null)
                sNew = UnderlyingEnvironmentState.Apply(a);

            CompoundFormula cfAndChoices = null;
            if (!bPropogateOnly && a.ContainsNonDeterministicEffect)
            {
                a = a.RemoveNonDeterminism(Time, out cfAndChoices);
            }

            PartiallySpecifiedState bsNew = new PartiallySpecifiedState(this, a);
            if (sNew != null)
            {
                bsNew.UnderlyingEnvironmentState = sNew;
                if (!bPropogateOnly && bsNew.Time != sNew.Time)
                    Debug.WriteLine("BUGBUG");

            }

            if (a.Effects != null)
            {
                if (a.HasConditionalEffects)
                {
                    List<CompoundFormula> lApplicableConditions = ApplyKnown(a.GetConditions());
                    bsNew.ApplyKnowledgeLoss(lApplicableConditions);
                    HashSet<Predicate> lAddEffects = new HashSet<Predicate>(), lRemoveEffects = new HashSet<Predicate>();
                    a.GetApplicableEffects(Known,lAddEffects, lRemoveEffects, true);
                    //first removing then adding
                    foreach (Predicate p in lRemoveEffects)
                        bsNew.AddEffect(p);
                    foreach (Predicate p in lAddEffects)
                        bsNew.AddEffect(p);
                    //bsNew.UpdateHidden(a, m_lObserved);
                    if(UseCFFBelief)
                        bsNew.UpdateHidden();
                }
                else
                {
                    bsNew.AddEffects(a.Effects);
                }
            }



            tsEffects += DateTime.Now - dtStart;
            dtStart = DateTime.Now;

            if (!bPropogateOnly && a.Observe != null)
            {
                //first applying the action (effects) and then observing
                fObserve = bsNew.UnderlyingEnvironmentState.Observe(a.Observe);

                bsNew.GeneratingObservation = fObserve;
                bsNew.AddObserved(fObserve);

                /*
                if (ReviseInitialBelief(fObserve))
                    bsNew.PropogateObservedPredicates();
                 * */
                if (!UseCFFBelief)
                {
                    if (m_bsInitialBelief.ReviseInitialBelief(fObserve, this))
                    {
                        if (SDRPlanner.UseCaching && !SDRPlanner.OptimizeMemoryConsumption)
                            bsNew.PropogateObservedPredicates();
                    }
                }
            }

            if (!bPropogateOnly && Predecessor != null)//the first one holds all knowns, to avoid propogation from the initial belief
                RemoveDuplicateObserved(bsNew.Known);//if p is true at t+1 and p is true at t, there is no point in maintaining the copy at t 

            tsObs += DateTime.Now - dtStart;


            if (bsNew != null && cfAndChoices != null)
                m_bsInitialBelief.AddInitialStateFormula(cfAndChoices);

            if (!bPropogateOnly && bsNew.Time != sNew.Time)
                Debug.WriteLine("BUGBUG");

            return bsNew;
        }

        private void RemoveDuplicateObserved(HashSet<Predicate> hObservedAtNextStep)
        {
            HashSet<Predicate> hsFiltered = new HashSet<Predicate>();
            foreach (Predicate p in Known)
            {
                if (!hObservedAtNextStep.Contains(p))
                    hsFiltered.Add(p);
            }
            Known = hsFiltered;
        }

        public Formula RegressObservation(Formula f)
        {
            /* There is no point in adding the observation, because it was already regressed
            CompoundFormula fWithObservation = new CompoundFormula("and");
            fWithObservation.AddOperand(f);
            if (GeneratingObservation != null)
                fWithObservation.AddOperand(GeneratingObservation);
            Formula fReduced = fWithObservation.Reduce(Observed);
             */
            Formula fReduced = f.Reduce(Known);
            Formula fToRegress = fReduced;
            if (fToRegress is CompoundFormula)
            {
                bool bChanged = false;
                //fToRegress = ((CompoundFormula)fToRegress).RemoveNestedConjunction(out bChanged).Simplify();
            }
            if (fToRegress.IsTrue(null))
                return fToRegress;
            if (fToRegress.IsFalse(null))
                Debug.Assert(false);
            HashSet<Predicate> hsMandatory = GeneratingAction.GetMandatoryEffects();
            if (fToRegress.IsTrue(hsMandatory))
                return new PredicateFormula(new GroundedPredicate(Domain.TRUE_PREDICATE));
            if (fToRegress.IsFalse(hsMandatory))
                return new PredicateFormula(new GroundedPredicate(Domain.FALSE_PREDICATE));

            if (GeneratingAction.HasConditionalEffects)
            {
                Formula fRegressed = fToRegress.Regress(GeneratingAction, Known);
                return fRegressed;
            }
            else
                return fToRegress;
        }

        //returns true if new things were learned
        private bool ReviseInitialBelief(Formula fObserve)
        {
            Formula fReduced = fObserve.Reduce(Known);
            
            Formula fToRegress = fReduced;
            if (fToRegress is CompoundFormula)
            {
                bool bChanged = false;
                fToRegress = ((CompoundFormula)fToRegress).RemoveNestedConjunction(out bChanged);
            }
            if (fToRegress.IsTrue(Known))
                return false;
            if (fToRegress.IsFalse(Known))
                Debug.Assert(false);
            if (Predecessor != null)
            {
                Formula fRegressed = fToRegress.Regress(GeneratingAction, Known);
                bool bPredecessorUpdated = ((PartiallySpecifiedState)Predecessor).ReviseInitialBelief(fRegressed);
                if (bPredecessorUpdated)
                {
                    bool bCurrentUpdated = PropogateObservedPredicates();
                    return bCurrentUpdated;
                }
                return false;
            }
            else
            {
                m_bsInitialBelief.AddReasoningFormula(fReduced);
                HashSet<Predicate> lLearned = ApplyReasoning();
                return lLearned.Count > 0;
            }
        }

        //returns true if new things were propogated
        public bool PropogateObservedPredicates()
        {
            
            Formula fObserve = null;

            GeneratingAction.IdentifyActivatedOptions(Predecessor.Known, Known);

 
            PartiallySpecifiedState pssAux = ((PartiallySpecifiedState)Predecessor).Apply(GeneratingAction, out fObserve, true);
            if (pssAux.Known.Count == Known.Count)
                return false;
            foreach (Predicate pObserve in pssAux.Known)
            {
                AddObserved(pObserve);
            }
            /*
            if (Predecessor.Observed.Count() > Observed.Count() + 4)
            {
                foreach (Predicate p in Predecessor.Observed)
                    if (!m_lObserved.Contains(p))
                        Debug.WriteLine(p);
                Debug.WriteLine("*");
            }
             * */
            return true;
        }


        public void ForgetPotentialEffects()
        {
            HashSet<Predicate> lPossibleEffects = new HashSet<Predicate>();
            foreach (CompoundFormula cf in GeneratingAction.GetConditions())
            {
                cf.Operands[1].GetAllPredicates(lPossibleEffects);
            }
            foreach (Predicate p in lPossibleEffects)
            {
                Predicate pNegate = p.Negate();
                if (Known.Contains(p))
                    RemoveObserved(p);
                else if (Known.Contains(pNegate))
                    RemoveObserved(pNegate);
                Hidden.Add(p.Canonical());
            }
        }

        //returns true if new things were propogated
        public HashSet<Predicate> PropogateObservedPredicates(HashSet<Predicate> lNewPredicates)
        {
            HashSet<Predicate> hsNextNewPredicates = new HashSet<Predicate>();

            GeneratingAction.IdentifyActivatedOptions(Predecessor.Known, Known);

            bool bNewForThisState = false;
            foreach (Predicate p in lNewPredicates)
                if (!Known.Contains(p))
                    bNewForThisState = true;
            //if (!bNewForThisState)
            //    return null;

            if (GeneratingAction.Effects != null)
            {
                GeneratingAction = GeneratingAction.ApplyObserved(lNewPredicates);
                HashSet<Predicate> lAdd = new HashSet<Predicate>();
                HashSet<Predicate> lRemove = new HashSet<Predicate>();
                HashSet<Predicate> lMandatory = GeneratingAction.GetMandatoryEffects();
                foreach (Predicate p in lMandatory)
                {
                    if (p.Negation)
                        lRemove.Add(p);
                    else
                        lAdd.Add(p);
                }
                foreach(Predicate p in lRemove)
                    if(!lAdd.Contains(p.Negate()))
                        if (AddObserved(p))
                            hsNextNewPredicates.Add(p);
                foreach (Predicate p in lAdd)
                    if (AddObserved(p))
                        hsNextNewPredicates.Add(p);



                //these are optional effects, so we are not sure whether the newly learned predicate will hold after the action, so we cannot propogate the knowledge - a forgetting mechanism
                HashSet<Predicate> lPossibleEffects = new HashSet<Predicate>();
                foreach (CompoundFormula cf in GeneratingAction.GetConditions())
                {
                    cf.Operands[1].GetAllPredicates(lPossibleEffects);
                }
                foreach (Predicate p in lPossibleEffects)
                {
                    Predicate pNegate = p.Negate();
                    if (lNewPredicates.Contains(p))
                        lNewPredicates.Remove(p);
                    else if (lNewPredicates.Contains(pNegate))
                        lNewPredicates.Remove(pNegate);

                }
            }


            //pretty sure that this is correct - for every new fact that was learned for the previous state, if it is not contradicted by the action, then it shold be added
            foreach (Predicate p in lNewPredicates)
            {
                if (!Known.Contains(p.Negate()))
                {
                    if(!SDRPlanner.OptimizeMemoryConsumption)
                        AddObserved(p);
                    hsNextNewPredicates.Add(p);
                }
            }

            return hsNextNewPredicates;
        }


        //returns true if new things were learned
        public HashSet<Predicate> ApplyReasoning()
        {
            /* not really doing here anything - is this a bug?
            List<Predicate> lHidden = new List<Predicate>();
            foreach (Predicate p in m_bsInitialBelief.Unknown)
            {
                if (p.Negation)
                {
                    if (!lHidden.Contains(p.Negate()))
                        lHidden.Add(p.Negate());
                }
                else
                {
                    if (!lHidden.Contains(p))
                        lHidden.Add(p);
                }
             
            }
             */
            HashSet<Predicate> lLearned = new HashSet<Predicate>();
            if (m_bsInitialBelief.Observed.Count() > Known.Count())
            {
                foreach (Predicate p in m_bsInitialBelief.Observed)
                    if (AddObserved(p))
                        lLearned.Add(p);
            }
            return lLearned;
        }
 
        //used to regress goal or precondition
        public bool RegressCondition(Formula f)
        {
            PartiallySpecifiedState pssCurrent = this;
            Formula fCurrent = f;
            while (pssCurrent != null)
            {
                Formula fReduced = fCurrent.Reduce(pssCurrent.Known);
                if (fReduced.IsTrue(null))
                    return true;
                if (fReduced.IsFalse(null))
                    return false;
                if (pssCurrent.Predecessor != null)
                {
                    if (pssCurrent.GeneratingAction.HasConditionalEffects)
                    {
                        Formula fRegressed = fReduced.Regress(pssCurrent.GeneratingAction);
                        fCurrent = fRegressed;
                    }
                }
                pssCurrent = (PartiallySpecifiedState)pssCurrent.Predecessor;

            }
            return false;
        }

        public override bool IsGoalState()
        {
            m_bsInitialBelief.MaintainProblematicTag = true;
            if (SDRPlanner.EnforceCNF)
            {
                bool bGoal = ConsistentWith(Problem.Goal.Negate(), false);
                if (bGoal)
                    return false;
                return true;
            }
            else
            {
                if (Problem.Goal is PredicateFormula)
                {
                    return RegressCondition(Problem.Goal);
                }
                else
                {
                    CompoundFormula cf = (CompoundFormula)Problem.Goal;
                    if (cf.Operator != "and")
                        throw new NotImplementedException();
                    foreach (Formula f in cf.Operands)
                        if (!RegressCondition(f))
                            return false;
                }
                
                 return true;
            }
        }

        public override State WriteTaggedDomainAndProblem(string sDomainFile, string sProblemFile, out int cTags, out MemoryStream msModels)
        {
            if (UseCFFBelief)
            {
                if (m_lPreviousTags == null || m_lFailureTag == null)
                {
                    int cRequiredTags = SDRPlanner.TagsCount;
                    CompoundFormula cfCNF = m_cfCNFBelief;
                    if (m_lFailureTag != null)
                    {
                        cRequiredTags--;
                        cfCNF = (CompoundFormula)m_cfCNFBelief.Clone();
                        CompoundFormula cfOr = new CompoundFormula("or");
                        foreach (Predicate p in m_lFailureTag)
                            cfOr.AddOperand(p.Negate());
                        cfCNF.AddOperand(cfOr);
                    }
                    throw new NotImplementedException();
                    m_lPreviousTags = null;// m_bsInitialBelief.RunSatSolver(cfCNF, cRequiredTags);
                }
                List<State> lStates = new List<State>();
                if (m_lFailureTag != null)
                {
                    lStates.Add(GetCurrentState(m_lFailureTag));
                    m_lFailureTag = null;
                }
                foreach (List<Predicate> lAssignment in m_lPreviousTags)
                {
                    State s = GetCurrentState(lAssignment);
                    if (!lStates.Contains(s))
                        lStates.Add(s);
                    if (lStates.Count == SDRPlanner.TagsCount)
                        break;
                }
                return m_bsInitialBelief.WriteTaggedDomainAndProblem(sDomainFile, sProblemFile, lStates, false, out cTags, out msModels);
            }
            else
                return WriteTaggedDomainAndProblem(sDomainFile, sProblemFile, new List<Action>(), out cTags, out msModels);
        }

        private State GetCurrentState(List<Predicate> lPredicates)
        {
            State s = new State(Problem);
            foreach (Predicate p in lPredicates)
            {
                if (p is TimePredicate)
                {
                    TimePredicate tp = (TimePredicate)p;
                    if (tp.Time == Time)
                    {
                        s.AddPredicate(tp.Predicate);
                    }
                }
            }
            foreach (Predicate p in Known)
                s.AddPredicate(p);
            return s;
        }

        private State WriteTaggedDomainAndProblem(string sDomainFile, string sProblemFile, List<Action> lActions, out int cTags, out MemoryStream msModels)
        {
            PartiallySpecifiedState pssCurrent = this;
            while (pssCurrent.Predecessor != null)
            {
                lActions.Insert(0, pssCurrent.GeneratingAction);
                pssCurrent = (PartiallySpecifiedState)pssCurrent.Predecessor;
            }
            return m_bsInitialBelief.WriteTaggedDomainAndProblem(sDomainFile, sProblemFile, lActions, out cTags, out msModels);
            /*
            if (Predecessor == null)
                return m_bsInitialBelief.WriteTaggedDomainAndProblem(sDomainFile, sProblemFile, lActions);
            lActions.Insert(0, GeneratingAction);
            return Predecessor.WriteTaggedDomainAndProblem(sDomainFile, sProblemFile, lActions);
             * */
        }

 
    }  
}

