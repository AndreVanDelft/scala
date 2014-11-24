/*
    This file is part of Subscript - an extension of the Scala language
                                     with constructs from Process Algebra.

    Subscript is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License and the
    GNU Lesser General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    Subscript consists partly of a "virtual machine". This is a library;
    Subscript applications may distribute this library under the
    GNU Lesser General Public License, rather than under the
    GNU General Public License. This way your applications need not
    be made Open Source software, in case you don't want to.

    Subscript is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You may have received a copy of the GNU General Public License
    and the GNU Lesser General Public License along with Subscript.
    If not, see <http://www.gnu.org/licenses/>
*/

package subscript.vm

import scala.util.{Try, Failure}
import scala.collection.mutable._
import subscript.vm.executor._
import subscript.vm.model.callgraph._
import subscript.vm.model.template.TemplateCodeHolder

object CodeExecutor {
  def defaultCodeFragmentExecutorFor(node: CallGraphNode, scriptExecutor: ScriptExecutor[_]): CodeExecutorTrait = {
    node match {
      case n@N_code_normal       (_) => new        NormalCodeFragmentExecutor(n, scriptExecutor)
      case n@N_code_unsure       (_) => new        UnsureCodeFragmentExecutor(n, scriptExecutor)
      case n@N_code_threaded     (_) => new      ThreadedCodeFragmentExecutor(n, scriptExecutor)
      case n@N_code_eventhandling(_) => new EventHandlingCodeFragmentExecutor(n, scriptExecutor)
      case _                    => new          TinyCodeExecutor(node, scriptExecutor)
    }
  }

  def executeCodeDirectly[N <: CallGraphNode, R](n: N): R =
    n.template.asInstanceOf[TemplateCodeHolder[R, N]].code(n)

  def executeCode[N <: CallGraphNode, R](n: N): R = {
    val template = n.template.asInstanceOf[TemplateCodeHolder[R,N]]
    executeCode(n, template.code(n))
  }
  def executeCode[N <: CallGraphNode, R](n: N, c: => R): R =
    n.codeExecutor.doCodeExecution(c)

  def executeCodeIfDefined[N <: CallGraphNode, R](n: N, code: ()=>R): R =
    if (code!=null) executeCode(n, code()) else null.asInstanceOf[R]

}

// Executors that execute any call to Scala code in the application:
// code fragments, script calls, parameter checks, tests in if and while, annotations
trait CodeExecutor // to make an empty class file so that ant will not get confused
trait CodeExecutorTrait extends subscript.vm.executor.parts.Tracer {
  // graph operations such as aaHappened may only be done when called from executor!
  
  var traceLevel = 0
  
  var canceled = false // TBD(?) inspect this flag before execution
  var regardStartAndEndAsSeparateAtomicActions = false

  def asynchronousAllowed: Boolean

  def doCodeExecution[R](code: => R): R = code
  private def shouldNotBeCalledHere = throw new Exception("Illegal Call")
  def executeAA     : Unit                                     = shouldNotBeCalledHere // TBD: clean up class/trait hierarchy so that this def can be ditched
  def executeAA(lowLevelCodeExecutor: CodeExecutorTrait): Unit = shouldNotBeCalledHere // TBD: clean up class/trait hierarchy so that this def can be ditched
  def afterExecuteAA: Unit                                     = afterExecuteAA_internal // TBD: clean up class/trait hierarchy so that this def can be ditched
  def afterExecuteAA_internal: Unit                            = shouldNotBeCalledHere // TBD: clean up class/trait hierarchy so that this def can be ditched
  def interruptAA   : Unit                                     = shouldNotBeCalledHere // TBD: clean up class/trait hierarchy so that this def can be ditched
  def n: CallGraphNode
  def scriptExecutor: ScriptExecutor[_]
  def cancelAA = canceled=true
}
case class TinyCodeExecutor(n: CallGraphNode, scriptExecutor: ScriptExecutor[_]) extends CodeExecutorTrait  { // TBD: for while, {!!}, @:, script call
  val asynchronousAllowed = false
  override def interruptAA   : Unit  = {} // TBD: clean up class/trait hierarchy so that this def can be ditched
  override def afterExecuteAA_internal: Unit  = {}
}
abstract class AACodeFragmentExecutor[R](_n: N_code_fragment[R], _scriptExecutor: ScriptExecutor[_]) extends CodeExecutorTrait  {

  // Executor for Atomic Actions. These require some communication with the ScriptExecutor, to make sure that
  // graph messages such as AAHappened en Success are properly sent.
  // Note: such messages may only be handled from the main ScriptExecutor loop!
  //
  // Since scala code execution from Subscript may be asynchronous (e.g., in the Swing thread or in a new thread),
  // there is some loosely communication with the ScriptExecutor
  // E.g., after calling the Scala code, the method executionFinished is called, which inserts an AAExecutionFinished
  def n = _n
  def scriptExecutor = _scriptExecutor
  val asynchronousAllowed = true
  override def interruptAA = {}
  override def cancelAA = super.cancelAA; interruptAA
  def naa = n.asInstanceOf[N_code_fragment[R]]
  def doCodeExecutionIn(lowLevelCodeExecutor: CodeExecutorTrait): Unit = lowLevelCodeExecutor.doCodeExecution{
      //n.hasSuccess  = true
      n.isExecuting = true
      n.$           = null

      try   {val r = CodeExecutor executeCodeDirectly n
             if (n.hasSuccess) {n.$ = scala.util.Success(r)}
            }
      catch {case f : Throwable => n.$ = Failure(f) }
      finally n.isExecuting = false

      executionFinished
  }
  def aaHappened(mode:AAHappenedMode) = {scriptExecutor.insert(AAHappened(n,null,mode))}
  def succeeded                       = {scriptExecutor.insert(SuccessMsg(n,null))}

  override def executeAA: Unit = executeAA(this) // for Atomic Action execution...should ensure that executionFinished is called
  override def executeAA(lowLevelCodeExecutor: CodeExecutorTrait): Unit = {
    n.hasSuccess = true
  } // for Atomic Action execution...should ensure that executionFinished is called

  // afterExecuteAA: to be called asynchronously by executor, 
  // in reaction to executionFinished (through the message queue, not through a call inside a call)
  final override def afterExecuteAA = { // finally notify; make sure things go synchronized
    scriptExecutor.doCodeThatInsertsMsgs_synchronized {afterExecuteAA_internal}
  }
  def afterExecuteAA_internal
  def executionFinished = { // make scriptExecutor call afterRun here, in its own message handling loop
    trace_nonl("executionFinished")
    scriptExecutor.doCodeThatInsertsMsgs_synchronized {
      scriptExecutor.insert(AAExecutionFinished(naa))
    }
  }
  def toBeReexecuted    = scriptExecutor.insert(AAToBeReexecuted   (naa)) // so that executor reschedules n for execution
  def deactivate        = scriptExecutor.insert(Deactivation       (naa,null,false))
  def suspend   = {}
  def resume    = {}
}

class NormalCodeFragmentExecutor[R](n: N_code_fragment[R], scriptExecutor: ScriptExecutor[_]) extends AACodeFragmentExecutor[R](n, scriptExecutor)  {
  //without the next two definitions the compiler would give the following error messages; TBD: get rid of these
  // class NormalCodeFragmentExecutor needs to be abstract, since:
  //   method scriptExecutor in trait CodeExecutorTrait of type => subscript.vm.ScriptExecutor is not defined
  //   method n in trait CodeExecutorTrait of type => subscript.vm.CallGraphNode[_ <: subscript.vm.TemplateNode] is not defined	CodeExecutor.scala	/subscript/src/subscript/vm	line 54	Scala Problem

  override def executeAA(lowLevelCodeExecutor: CodeExecutorTrait): Unit = {
    super.executeAA(lowLevelCodeExecutor)
    if (regardStartAndEndAsSeparateAtomicActions) aaHappened(DurationalCodeFragmentStarted)
    doCodeExecutionIn(lowLevelCodeExecutor)
  }
  override def afterExecuteAA_internal = {
    if (!n.isExcluded) {
       aaHappened( if (regardStartAndEndAsSeparateAtomicActions) DurationalCodeFragmentEnded else AtomicCodeFragmentExecuted)
       succeeded; deactivate
    }
  }
}
class UnsureCodeFragmentExecutor[R](n: N_code_unsure[R], scriptExecutor: ScriptExecutor[_]) extends AACodeFragmentExecutor[R](n, scriptExecutor)  {
  override def executeAA(lowLevelCodeExecutor: CodeExecutorTrait): Unit = {
    super.executeAA(lowLevelCodeExecutor)
    doCodeExecutionIn(lowLevelCodeExecutor)
  }
  override def afterExecuteAA_internal = {
    if (n.hasSuccess) {
       aaHappened(AtomicCodeFragmentExecuted); succeeded; deactivate
    }
    else if (n.result==ExecutionResult.Ignore){ // allow for deactivating result
      toBeReexecuted
    }
    else {
      deactivate
    }
  }
}
// Adapter to wrap around other CodeExecutors
// TBD: improve
trait CodeExecutorAdapter[R,CE<:CodeExecutorTrait] extends CodeExecutorTrait {
  var adaptee: CE = _
  def adapt[R](codeExecutor: CE) = {adaptee = codeExecutor}
  def asynchronousAllowed = adaptee.asynchronousAllowed
}
class ThreadedCodeFragmentExecutor[R](n: N_code_threaded[R], scriptExecutor: ScriptExecutor[_]) extends NormalCodeFragmentExecutor[R](n, scriptExecutor)  {
  override def interruptAA: Unit = if (myThread!=null) try myThread.interrupt catch {case _: InterruptedException =>}  // Don't pollute the outout
  regardStartAndEndAsSeparateAtomicActions = true
  var myThread: Thread = null

  override def doCodeExecutionIn(lowLevelCodeExecutor: CodeExecutorTrait): Unit = {
      val runnable = new Runnable {
        def run() {
          ThreadedCodeFragmentExecutor.super.doCodeExecutionIn(lowLevelCodeExecutor) // does scriptExecutor.insert(AAExecutionFinished)
        }
      }
      myThread = new Thread(runnable)
      myThread.start()
  }
}
class SwingCodeExecutorAdapter[R,CE<:CodeExecutorTrait] extends CodeExecutorAdapter[R,CE]{
  def n = adaptee.n
  def scriptExecutor = adaptee.scriptExecutor

  override def      executeAA: Unit = {
    adaptee.regardStartAndEndAsSeparateAtomicActions = adaptee.asynchronousAllowed
    adaptee.executeAA(this) // Not to be called? TBD: clean up class/trait hierarchy
  }
  override def afterExecuteAA_internal: Unit = adaptee.afterExecuteAA_internal  // TBD: clean up class/trait hierarchy so that this def can be ditched
  override def    interruptAA: Unit = adaptee.interruptAA     // TBD: clean up class/trait hierarchy so that this def can be ditched
  override def doCodeExecution[R](code: =>R): R = {

    // we need here the default value for R (false, 0, null or a "Unit")
    // for some strange reason, the following line would go wrong:
    //
    // var result: R = _
    //
    // A solution using a temporary class was found at
    // http://missingfaktor.blogspot.com/2011/08/emulating-cs-default-keyword-in-scala.html
    var result: R = null.asInstanceOf[R]
    // luckily we have the default value for type R now...

    if (adaptee.asynchronousAllowed) {
      var runnable = new Runnable {
        def run(): Unit = {result = adaptee.doCodeExecution(code)}
      }
      javax.swing.SwingUtilities.invokeLater(runnable)
    }
    else {
      var runnable = new Runnable {
        def run(): Unit = {result = adaptee.doCodeExecution(code)}
      }
      javax.swing.SwingUtilities.invokeAndWait(runnable)
    }
    result
  }
}
case class EventHandlingCodeFragmentExecutor[R](_n: N_code_fragment[R], _scriptExecutor: ScriptExecutor[_])
   extends AACodeFragmentExecutor[R](_n, _scriptExecutor)  {

  private var busy = false

  override def executeAA(lowLevelCodeExecutor: CodeExecutorTrait): Unit = executeMatching(true) // dummy method needed because of a flaw in the class hierarchy
  def executeMatching(isMatching: Boolean): Unit = {  // not to be called by scriptExecutor, but by application code
    if (busy) return
    _n.hasSuccess = isMatching
    if (isMatching)
    {
      busy = true
      _n.hasSuccess  = true
      _n.isExecuting = true
      _n.$           = null

      try   {val r = CodeExecutor executeCode _n
                   if (_n.hasSuccess) _n.$ = scala.util.Success(r)
            }
      catch {case f : Throwable => _n.$ = Failure(f) }
      finally _n.isExecuting = false

     // if (n.hasSuccess)  maybe this test should be activated
     //{
       executionFinished // will probably imply a call back to afterExecute from the ScriptExecutor thread
                         // TBD: maybe a provision should be taken here to prevent handling a second event here, in case this is a N_code_eh
    //}
    }
  }
  override def afterExecuteAA_internal: Unit = {
      if (_n.isExcluded || !n.hasSuccess) return
      _n match {
        case eh:N_code_eventhandling[_] =>
          aaHappened(AtomicCodeFragmentExecuted)
          succeeded
          deactivate

        case eh:N_code_eventhandling_loop[_] =>
             busy = false   // ??? should the same executor really be able to "fire" twice ???
             aaHappened(AtomicCodeFragmentExecuted)
             eh.result match {
                case ExecutionResult.Success       =>
                case ExecutionResult.Break         => succeeded
                case ExecutionResult.OptionalBreak => succeeded; deactivate
             }
      }
  }
}
