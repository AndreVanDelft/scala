package life

import scala.math._
import scala.swing._
import scala.swing.event._
import subscript.Predef._
import subscript.swing.SimpleSubscriptApplication
import subscript.swing.Scripts._
import subscript._
import subscript.DSL._
import subscript.Predef._
import subscript.vm._

object LifeFrame extends LifeFrameApplication
class LifeFrameApplication extends BasicLifeFrameApplication {

    //////////////////////////////////////////////
    // speed control
    //////////////////////////////////////////////
    
    def getSleep_ms = pow(2, 12-speed).toInt // logarithmic scale
    
    def sleep = 
      try {
        val sleepPart_ms = 10
        val startTime_ms = System.currentTimeMillis
        while (System.currentTimeMillis - startTime_ms < getSleep_ms) {
          Thread.sleep(sleepPart_ms)
        }
      }
      catch { case e: InterruptedException => /*println("sleep interrupted")*/}

    def sleep_ms(time_ms: Int) = 
      try {
          Thread.sleep(time_ms)
      }
      catch { case e: InterruptedException => println("sleep interrupted")}

    //////////////////////////////////////////////
    // confirm exit dialog
    //////////////////////////////////////////////
    def confirmExit: Boolean = Dialog.showConfirmation(top.contents.head, "Are you sure?", "About to exit")==Dialog.Result.Yes
     
    board.listenTo(board.mouse.clicks)
    board.listenTo(board.mouse.moves)

    //////////////////////////////////////////////
    // handle MouseDown events
    //////////////////////////////////////////////
     def resetLastMousePos: Unit = board.resetLastMousePos // so that mouseDragSet will initially not draw a line
     
     def handleMouseSingleClick(p: java.awt.Point): Unit = {
       selectedPattern match {
          case None => board.mouseDownToggle(p)
          case Some(s) => val ec = Coord(p.x/board.cellSizeX, p.y/board.cellSizeY)
                          for (pc <- ConwayPatterns.moveTo(s,ec)) {board.setCellValue(pc.x,pc.y,true)}
       }
     }
     def handleMouseMove(p: java.awt.Point): Unit = board.mouseDragSet(p)
     def handleMouseDrag(p: java.awt.Point): Unit = board.mouseDragSet(p)
    
     def chr(c:Any) = c.asInstanceOf[Int].toChar
     
  implicit def script..
  
    key(c??: Char     ) =  key2(top, ActualAdaptingParameter(_c))  //key(top, c??) // TBD in subscript-scalac parser: recognize "??" and "?"
   vkey(k??: Key.Value) = vkey2(top, ActualAdaptingParameter(_k)) //vkey(top, k??)

def script..
	 randomizeCommand  = randomizeButton + 'r'
	     clearCommand  =     clearButton + 'c'
	      stepCommand  =      stepButton + ' '
	      exitCommand  =      exitButton + windowClosing,top
	multiStepStartCmd  =     startButton + Key.Enter
	 multiStepStopCmd  =      stopButton + Key.Enter
	
	doExit             =   exitCommand var r:Boolean=false @{gui(there)}: {r=confirmExit} while (!r)
	
       boardControl    = ...; noise / (..singleStep) multiStep || clear || randomize

      do1Step          = {*board.calculateGeneration*} @{gui(there)}: {!board.validate!}
      
      noise            = 'n'; ... @{gui(there)}: board.doRandomize {*sleep*}
      randomize        =   randomizeCommand @{gui(there)}: {!board.doRandomize()!}
      clear            =       clearCommand @{gui(there)}: {!board.doClear!}
      singleStep       =        stepCommand do1Step
       multiStep       = multiStepStartCmd; ... do1Step {*sleep*} 
                       / multiStepStopCmd

      speedControl     = ...; speedKeyInput + speedButtonInput + speedSliderInput
                    
    setSpeed(s: Int)   = @{gui(there)}: {!setSpeedValue(s)!}

      speedKeyInput    = times(10) 
                       + val c:Any=(pass_up1(here)+'0') key(chr(c)) setSpeed(digit2Speed(chr(c))) // TBD: make here an implicit parameter
                              
   speedButtonInput = if (speed>minSpeed) speedDecButton
                    + if (speed<maxSpeed) speedIncButton
    
     speedDecButton = minSpeedButton setSpeed,minSpeed + slowerButton setSpeed(speed-1)
     speedIncButton = maxSpeedButton setSpeed,maxSpeed + fasterButton setSpeed(speed+1)
     
   speedSliderInput = speedSlider setSpeed,speedSlider.value

      mouseInput    = (mouseClickInput & mouseDragInput)
                    /  doubleClick (mouseMoveInput / doubleClick {!resetLastMousePos!})       ; ...

 //mouseClickInput  = mouseSingleClick (board, p?:java.awt.Point) {! doMouseSingleClick(p) !} ... 
//                     !@#%^&$ mouseSingleClick also reacts on double clicks!!! 
//                     So wait 220 ms; if by then no mouseDoubleClick as arrived, do the singleClick action:
   mouseClickInput  = var p:java.awt.Point=null
                    ; var doubleClickTimeout:Boolean=false 
                      mouseSingleClick( board, ActualOutputParameter(p, (v:java.awt.Point)=>p=v)) 
                      {! resetLastMousePos !}
                      ( {*sleep_ms(220); println("timeout"); doubleClickTimeout=true*}
                      / mouseDoubleClick( board, ActualOutputParameter(p, (v:java.awt.Point)=>p=v)))
                      while (!doubleClickTimeout)
                    ; {! handleMouseSingleClick(p) !}
                    ; ...
                    
   doubleClick      = var p:java.awt.Point=null mouseDoubleClick(board, ActualOutputParameter(p, (v:java.awt.Point)=>p=v)) // TBD: "p?"
   mouse_Released   = var p:java.awt.Point=null mouseReleased(   board, ActualOutputParameter(p, (v:java.awt.Point)=>p=v)) // TBD: "p?"; mouseReleased instead of mouse_Released yields "too many arguments for method" error
    mouseDragInput  = mouseDraggings(board, (e: MouseEvent) => handleMouseDrag(e.point)) / (mouse_Released  {!resetLastMousePos!}); ...
    mouseMoveInput  = mouseMoves(    board, (e: MouseEvent) => handleMouseMove(e.point)) 
  //mouseMoveToggle = var p:java.awt.Point=null mouseMove(board, p?) // doMouseDraw(p))  

override def script..
    live            = ||  boardControl mouseInput speedControl doExit
                   
}


