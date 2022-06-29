using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Diagnostics;

namespace PDDL
{
    public abstract class DynamicBeliefState
    {
        public static int STATE_COUNT = 0;
        public int ID { get; protected set; }

        public int Time { get; protected set; }

        public State UnderlyingEnvironmentState { get; set; }
        public DynamicBeliefState Predecessor { get; protected set; }
        public Problem Problem { get; protected set; }
        public Domain Domain { get; protected set; }
        public HashSet<Predicate> Known { get; protected set; }
        public HashSet<Predicate> Hidden { get; protected set; }
        public Action GeneratingAction { get; protected set; }
        public Formula GeneratingObservation { get; protected set; }
        public Dictionary<string, double> FunctionValues { get; protected set; }


        public abstract DynamicBeliefState Apply(string sAction, out Formula fObserved);
        public abstract DynamicBeliefState Apply(Action a, out Formula fObserved);
        public abstract bool IsGoalState();
        public abstract State WriteTaggedDomainAndProblem(string p, string p_2, out int cTags, out System.IO.MemoryStream msModels);

        public abstract bool ConsistentWith(Formula formula, bool bCheckingActionPreconditions);

        public abstract bool ConsistentWith(Predicate p, bool bCheckingActionPreconditions);

        public bool ConsistentWith(State s)
        {
            foreach (Predicate pState in Known)
            {
                if (!s.ConsistentWith(pState))
                    return false;
            }
            return true;
        }

        protected List<CompoundFormula> ApplyKnown(List<CompoundFormula> lConditions)
        {
            List<CompoundFormula> lClean = new List<CompoundFormula>();
            foreach (CompoundFormula cfCondition in lConditions)
            {
                if (!cfCondition.Operands[0].IsTrue(Known))//in this case thre is no reasoning - conditional effects are known
                {
                    if (!cfCondition.Operands[0].IsFalse(Known))//in this case the rule does not apply, so no valuable reasoning
                    {
                        CompoundFormula cfClean = new CompoundFormula("when");
                        if ((cfCondition.Operands[0]) is CompoundFormula)
                            cfClean.AddOperand(((CompoundFormula)cfCondition.Operands[0]).RemovePredicates(Known));
                        else
                        {
                            PredicateFormula pf = (PredicateFormula)(cfCondition.Operands[0]);
                            if (!Known.Contains(pf.Predicate))
                                cfClean.AddOperand(pf);
                            else
                                cfClean.AddOperand(new CompoundFormula("and"));
                        }
                        cfClean.AddOperand(cfCondition.Operands[1]);
                        lClean.Add(cfClean);
                    }
                }
            }
            return lClean;
        }


        //forget effects only if they currently have a known value and that value might change
        protected void ApplyKnowledgeLoss(List<CompoundFormula> lConditions)
        {
            HashSet<Predicate> lAllEffectPredicates = new HashSet<Predicate>();
            foreach (CompoundFormula cfCondition in lConditions)
            {//for now assuming that when clause is only a simple conjunction
                lAllEffectPredicates.UnionWith(cfCondition.Operands[1].GetAllPredicates());
            }
            foreach (Predicate pEffect in lAllEffectPredicates)
            {
                Predicate pNegate = pEffect.Negate();
                if (Known.Contains(pNegate))
                {
                    AddHidden(pNegate);
                }
            }
        }

        protected void AddHidden(Predicate pHidden)
        {
            RemoveObserved(pHidden);
            Hidden.Add(pHidden.Canonical());

        }
        protected void AddHidden(Formula f)
        {
            if (f is PredicateFormula)
                AddHidden(((PredicateFormula)f).Predicate);
            else
            {
                CompoundFormula cf = (CompoundFormula)f;
                if (cf.Operator != "and")
                    throw new NotImplementedException();
                foreach (Formula fSub in cf.Operands)
                    AddHidden(fSub);
            }
        }

        public virtual bool AddObserved(Predicate p)
        {
            if (p is ParametrizedPredicate)
                throw new NotImplementedException();
            if (p.Name == Domain.TRUE_PREDICATE)
                return false;

 
            return AddToObservedList(p);
        }

        protected bool AddToObservedList(TimePredicate tp)
        {
            if (tp.Time == Time)
                return AddToObservedList(tp.Predicate);
            return ((PartiallySpecifiedState)Predecessor).AddToObservedList(tp);
        }

        protected bool RemoveObserved(Predicate p)
        {
            bool bFound = Known.Remove(p);
            return bFound;
        }

        protected bool AddToObservedList(Predicate p)
        {
#if DEBUG
            if (p.Name != "Choice" && !p.Negation)
            {
                Debug.Assert(UnderlyingEnvironmentState == null || (UnderlyingEnvironmentState.Contains(p)), "Adding a predicate that does not exist");
                if (UnderlyingEnvironmentState != null && !UnderlyingEnvironmentState.Contains(p))
                    Console.WriteLine("Adding a predicate that does not exist");
            }
#endif

            if (p.Name == "good" && !p.Negation)
                Console.Write("*");

            if (Known.Contains(p))
                return false;

            //if (p.ToString() == "(not (at-x p-1))")
            //   Console.WriteLine("*");

            Predicate pNegate = p.Negate();
            if (Known.Contains(pNegate))
                RemoveObserved(pNegate);
            Known.Add(p);
            Hidden.Remove(p.Canonical());
            
            return true;
        }

        public bool AddObserved(HashSet<Predicate> l)
        {
            bool bUpdated = false;
            foreach (Predicate p in l)
                if (AddObserved(p))
                    bUpdated = true;
            return bUpdated;
        }

        public HashSet<Predicate> AddObserved(Formula f)
        {
            HashSet<Predicate> hsNew = new HashSet<Predicate>();
            if (f is PredicateFormula)
            {
                Predicate p = ((PredicateFormula)f).Predicate;
                if (AddObserved(p))
                    hsNew.Add(p);
            }
            else
            {
                CompoundFormula cf = (CompoundFormula)f;
                if (cf.Operator == "and")
                    foreach (Formula fSub in cf.Operands)
                        hsNew.UnionWith(AddObserved(fSub));
                else
                {
                    //do nothing here - not adding formulas currently, only certainties
                    //throw new NotImplementedException();
                }
            }
            return hsNew;
        }

        protected void AddEffects(Formula fEffects)
        {
            if (fEffects is PredicateFormula)
            {
                AddEffect(((PredicateFormula)fEffects).Predicate);
            }
            else
            {
                CompoundFormula cf = (CompoundFormula)fEffects;
                if (cf.Operator == "oneof")
                {
                    foreach (Formula f in cf.Operands)
                        AddHidden(f);
                }
                else if (cf.Operator != "and")
                    throw new NotImplementedException();
                else
                {
                    HashSet<Predicate> lRemove = new HashSet<Predicate>();
                    HashSet<Predicate> lAdd = new HashSet<Predicate>();
                    foreach (Formula f in cf.Operands)
                    {
                        if (f is PredicateFormula)
                        {
                            Predicate p = ((PredicateFormula)f).Predicate;
                            if (p.Negation)
                                lRemove.Add(p);
                            else
                                lAdd.Add(p);
                        }
                        else
                            AddEffects(f);
                    }
                    foreach (Predicate p in lRemove)
                    {
                        if (!lAdd.Contains(p.Negate()))
                            AddEffect(p);
                    }
                    foreach (Predicate p in lAdd)
                        AddEffect(p);
                }
            }
        }

        protected virtual void AddEffect(Predicate pEffect)
        {
            if (Problem.Domain.IsFunctionExpression(pEffect.Name))
            {
                GroundedPredicate gpIncreaseDecrease = (GroundedPredicate)pEffect;
                double dPreviousValue = Predecessor.FunctionValues[gpIncreaseDecrease.Constants[0].Name];
                double dDiff = double.Parse(gpIncreaseDecrease.Constants[1].Name);
                double dNewValue = double.NaN;
                if (gpIncreaseDecrease.Name.ToLower() == "increase")
                    dNewValue = dPreviousValue + dDiff;
                else if (gpIncreaseDecrease.Name.ToLower() == "decrease")
                    dNewValue = dPreviousValue + dDiff;
                else
                    throw new NotImplementedException();
                FunctionValues[gpIncreaseDecrease.Constants[0].Name] = dNewValue;
            }
            else if (!Known.Contains(pEffect))
            {
                Predicate pNegateEffect = pEffect.Negate();
                if (Known.Contains(pNegateEffect))
                {
                    //Debug.WriteLine("Removing " + pNegateEffect);
                    RemoveObserved(pNegateEffect);
                }
                //Debug.WriteLine("Adding " + pEffect);
                AddObserved(pEffect);
            }
        }

        public override string ToString()
        {
            foreach (Predicate p in Known)
                if (p.Name == "at" && !p.Negation)
                    return p.ToString();
            return "";
        }
        public override int GetHashCode()
        {
            return ToString().GetHashCode();
        }

        protected void UpdateHidden()
        {
            //bugbug; // there must be a better implementation!

            //we handle here only a very special case, where p->~p, and we don't have q->p. In this case either ~p was true before the action, or p was true and now we have ~p.
            //there is a more general case where when either p or ~p was correct before the action, q should hold after it, but we do not handle it here.


            //we need to check every condition that has pHidden as an effect
            List<Predicate> lPreviouslyHidden = new List<Predicate>(Hidden);



            foreach (Predicate pHidden in lPreviouslyHidden)
            {
                Predicate pNegateHidden = pHidden.Negate();

                List<CompoundFormula> lAddsP = new List<CompoundFormula>(), lRemovesP = new List<CompoundFormula>();
                foreach (CompoundFormula cf in GeneratingAction.GetConditions())
                {
                    HashSet<Predicate> lEffects = cf.Operands[1].GetAllPredicates();
                    if (lEffects.Contains(pHidden))
                    {
                        lAddsP.Add(cf);
                        break;
                    }
                    else if (lEffects.Contains(pNegateHidden))
                        lRemovesP.Add(cf);
                }

                //handling here only the case: ~p->p, there is an opposite case p->~p, but there is no domain that uses that, so we don't implement it.
                if (lAddsP.Count > 0)
                {
                    //nothing to check here - p could be added, so we cannot conclude that ~p holds afterwards
                    continue;
                }
                if (lRemovesP.Count > 0)
                {
                    List<Predicate> lObserved = new List<Predicate>();
                    lObserved.Add(pHidden);
                    foreach (CompoundFormula cf in lRemovesP)
                    {
                        if (cf.Operands[0].IsTrue(lObserved))//if p then ~p, so either ~p before the action, or p and then ~p after the action
                        {
                            AddObserved(pNegateHidden);
                            break;
                        }
                    }
                }
            }

        }


    }
}
