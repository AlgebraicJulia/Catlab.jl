## Parse Julia Programs 
# The purpose of this documentation is to provide a tutorial on the functionality of the ParseJuliaPrograms file.
# This tutorial will provide a brief overview on each of the functions and how a wiring diagram is parsed from
# a Julia function expression.

# ## Program Macro
#
macro program(pres, exprs...)
    Expr(:call, GlobalRef(ParseJuliaPrograms, :parse_wiring_diagram),
        esc(pres), (QuoteNode(expr) for expr in exprs)...)
end

# This macro is the definition for the macro @program where it takes in the presentation and the list of ast expressions as parameters
# Expr creates an expression where :call indicates the expression is a function call and
# GlobalRef creates a reference to the function being called, 
# with ParseJuliaPrograms being the module and parse_wiring_diagram the function called.
# Esc allows the presentation to be evaluated in the context of the caller rather than the macro's scope.
# QuoteNode takes each expression from the list of ast expressions passed in to create a quoted expression.
# Syntax:
@program(pres, exprs...)


# ## Parse Wiring Diagram
#
function parse_wiring_diagram(pres::Presentation, expr::Expr)::WiringDiagram
    @match expr begin
      Expr(:function, call, body) => parse_wiring_diagram(pres, call, body)
      Expr(:->, call, body) => parse_wiring_diagram(pres, call, body)
      _ => error("Not a function or lambda expression")
    end
end

# This function parses a wiring diagram from a Julia function expression where it takes in the presentation and a given expression as parameters.
# 