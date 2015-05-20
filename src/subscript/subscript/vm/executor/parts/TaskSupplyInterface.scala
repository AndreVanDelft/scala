package subscript.vm.executor.parts

import subscript.vm._
import subscript.vm.executor._
import subscript.vm.executor.data._
import subscript.vm.model.template._
import subscript.vm.model.template.concrete._
import subscript.DSL._
import subscript.vm.model.callgraph.CallGraphNode

trait TaskSupplyInterface {this: ScriptExecutor[_] =>
  def invokeFromET(f: => Unit) = msgQueue insert InvokeFromET(graph.rootNode, () => f)
  
  def launch[R](n: CallGraphNode, aScript: ScriptNode[R])  {
    val launchAnchor       = CallGraphNode.getLowestLaunchAnchorAncestor(n) // could be rootNode
    val callAnchorTemplate =     T_call[R]("<launched>", null)
    val callAnchorNode     =     N_call(callAnchorTemplate)
    CallGraph.connect(parentNode = launchAnchor, childNode = callAnchorNode, scriptNode = launchAnchor.scriptNode)
    CallGraph.connect(parentNode = callAnchorNode, childNode = aScript, scriptNode = launchAnchor.scriptNode) // code duplicated from Callgraph.activateFrom
    msgQueue insert Activation(aScript)                                 // idem
  }
  
}