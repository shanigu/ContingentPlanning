using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

namespace PDDL
{
    class ParametrizedAction : Action
    {
        public List<Parameter> Parameters { get; private set; }
        public ParametrizedAction(string sName)
            : base(sName)
        {
            Parameters = new List<Parameter>();
            ParameterNameToType = new Dictionary<string, string>();
        }
        public Dictionary<string, string> ParameterNameToType { get; private set; }
        public void AddParameter(Parameter parameter)
        {
            Parameters.Add(parameter);
            ParameterNameToType[parameter.Name] = parameter.Type;
        }
        public override Action Clone()
        {
            ParametrizedAction aNew = new ParametrizedAction(Name);
            aNew.Parameters = Parameters;
            if (Preconditions != null)
                aNew.Preconditions = Preconditions.Clone();
            if (Effects != null)
                aNew.SetEffects( Effects.Clone());
            if( Observe != null )
                aNew.Observe = Observe.Clone();
            aNew.HasConditionalEffects = HasConditionalEffects;
            aNew.ContainsNonDeterministicEffect = ContainsNonDeterministicEffect;
            return aNew;
        }
    }
}
