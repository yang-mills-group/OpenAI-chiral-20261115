import ZecaRelic
set_option autoImplicit false
set_option maxHeartbeats 270000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Seld.Zeca
open Function Filter Metric Set MeasureTheory OS OS.Semigroup Complex
open scoped Topology BigOperators NNReal ENNReal InnerProductSpace ComplexOrder


namespace Monument
open Poin Boundary Probe

/- Free tag for recovering the exact priced word model prior to boosts. -/
variable {H : Hilbert}

open WithLp
abbrev CW:=colorP 2
def twistX (f:CW):CW:= toLp 2 (fun i=>star (f (1-i)))
def twistL : CW →SL[starRingEnd ℂ] CW where
 toFun:=twistX
 map_add' a b:=by
   ext i
   change star (a (1-i)+b (1-i))=star (a (1-i))+star (b (1-i))
   simp
 map_smul' a b:=by
   ext i
   change star (a*b (1-i))=star a*star (b (1-i))
   simp
 cont:=by
   unfold twistX
   fun_prop

def plain(n:ℕ):Pattern where
 amount:=2
 charge:=n
 dual:=twistL
 invol v:= by ext i; change star (star (v (1-(1-i))))=v i; simp
 E:=1
 L:=1
 Ec:=continuous_const
 Lc:=continuous_const
 pin _ _:= rfl
 link _ _:=1
 ink _ _:=analyticAt_const
 base _ _:=rfl
 journey _ _:=rfl
 shared _ _:=rfl

def announce (D:Moment H): CW →L[ℂ] H.Op where
 toFun u:= (u 0) • D.op + (u 1) • star D.op
 map_add' a b:=by
   change (a 0+b 0) • D.op + (a 1+b 1) • star D.op = _
   rw [add_smul,add_smul]; abel
 map_smul' a b:=by
   change (a*b 0) • D.op + (a*b 1) • star D.op = a • _
   rw [mul_smul,mul_smul,←smul_add]
 cont:=by fun_prop

/-- One primary D together with adjoint as a multiplet.
(E and L here irrelevant and don't ascribe any scalar restoration.)
-/
def Quadra(D:Moment H) : Canopy H Unit where
 P _:=plain D.n
 flash _:=announce D
 duplex _ x:=by
  change CW at x
  have e:(1-(1:Fin 2))=0:=by decide
  have f:(1-(0:Fin 2))=1:=by decide
  change star (x (1-(0:Fin 2))) • D.op + star (x (1-(1:Fin 2))) • star D.op=star (x 0•D.op+x 1• star D.op)
  rw [e,f,star_add,star_smul,star_smul,star_star,add_comm]

def qPrimary(D:Moment H):(Quadra D).Chip:= ⟨(),toLp 2 ![1,0]⟩
lemma qPrice(D:Moment H):letter (Quadra D) (qPrimary D)=D:=by
 let a:=D.op
 change (⟨D.n,(1:ℂ) • D.op + (0:ℂ) • star D.op⟩:Moment H)=D
 rw [zero_smul, one_smul,add_zero]
#print axioms qPrice
