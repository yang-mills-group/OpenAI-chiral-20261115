import YM.SU5.Selected.Cor.Bright
import YM.SU5.Selected.Rail.Carte
/-! # Propagate into full Single of six slots. New stencils from Rail.
window pending. Use $λ$ exponents ℕ.
-/
set_option autoImplicit false
set_option maxHeartbeats 350000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Pannier.Chancel.Cuve
open Function Filter NormedSpace Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory ProbabilityTheory Peaks Drapes Rush Tulip Dial Pastry
open Buffered Branch Tenant Skye RG
open Crest Rail Airy Lantern
open Lantern.Bulb
open Reed (Fine)
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
set_option synthInstance.maxSize 24000
local notation "I"=> Complex.I
local notation "PS" N:max => cutM (Tset N)
local notation "P" N:max => freeze (fun _:Site N=> Fir.Aop)
variable {k n l:ℕ}{N:Side} (M:Tulip.Male)
local notation "Ω" N:max=> (1: Pane N)
def spinView(N:Side)(A:Op (SpinN N)): Op (Single N):= A ⊗ₖ (1:Op SU.Slot)
def TilePure :Prop := spar 4 M (Ω N)= spinView N (tip N M)
#print TilePure
lemma upperP (N:Side): PS N=spinView N (P N):=by
 let T:= (fun _:Bloch.Momentum=> Fir.Aop); have he: P N=jump (Equiv.refl _) (fun _=> Fir.Aop):=(freeze_square (N:=N) T).symm.trans (pilesV Fir.Aop)
 rw [he]; ext ⟨⟨x,s⟩,i⟩ ⟨⟨y,t⟩,j⟩;
 have hk: ((x,s),i)∈ Tset N↔s∈plusHalf:=Window.mem_Tset ..; rw [spinView,Matrix.kronecker_apply,jump_apply, Fir.Adef,←Lat.raising]; by_cases p:x=y <;> by_cases u:s=t <;> by_cases h:i=j <;> simp [cutM,p,u,h,Matrix.one_apply,Window.mem_Tset] -- Tset membership tune
variable {q q' α β:Type*}[Fintype q][DecidableEq q][Fintype q'][DecidableEq q'][Fintype α][DecidableEq α][Fintype β][DecidableEq β]
abbrev Screen (F: WRect α q): WRect (α × SU.Slot) (q × SU.Slot):= F ⊗ₖ (1:Op SU.Slot)
lemma tap_cost (F:WRect α q): ‖Screen F‖≤‖F‖:= warp_bound F SU.Slot
lemma tap_times (F:WRect β α)(X:WRect α q): Screen F * Screen X= Screen (F*X):=by unfold Screen; rw [←Matrix.mul_kronecker_mul, mul_one]
lemma tap_sub (F G:WRect α q): Screen (F-G)= Screen F-Screen G:= warp_sub ..
lemma tap_self (X:Op q)(p:ℕ): Screen X^p = Screen (X^p):=by induction p with| zero=> rw [pow_zero,pow_zero]; exact Matrix.one_kronecker_one.symm|succ p ih=>rw [pow_succ,pow_succ,ih,tap_times]
variable (Z:q→ basisRule)(W:FaceL) (u: Site N)
def hiveX (W:FaceL)(n t:ℕ)(u:Site N):= Screen (clerks W N u n t)
abbrev hiveV(q:Type*) : Type _ := q× SU.Slot
def hiveY (k:ℕ): WRect (Single N) (hiveV q):= Screen (chamberU Z N u M k)
def rootV (k:ℕ) := Screen (exactU Z N u k)
#print hiveY
local notation "dA" k:max=> hiveY M Z u k
local notation "dV" k:max=> rootV Z u k
-- power essential
lemma spirit (n t:ℕ): (1-PS N)* hiveX W n t u= hiveX W n t u:=by
 have ha:1-PS N=Screen (1-P N):=by rw [upperP,tap_sub,show Screen (1:Op (SpinN N))=1 from Matrix.one_kronecker_one]; rfl
 unfold hiveX; rw [ha,tap_times,clover]
lemma hearty (k:ℕ): PS N * dA k=dV k:=by rw [upperP]; exact (tap_times _ _).trans (congrArg Screen (Rail.hidden ..))
lemma hearty_s (p:TilePure (N:=N) M)(k:ℕ): spar 4 M (Ω N)* dA k=dA k:=by rw [p]; exact (tap_times _ _).trans (congrArg Screen (adheres ..))
lemma gramS(n t k:ℕ): (hiveX W n t u)ᴴ* dA k=Screen (balanceA W Z t n k M N):=by
 unfold hiveX hiveY Screen; rw [Matrix.conjTranspose_kronecker,Matrix.conjTranspose_one, ←Matrix.mul_kronecker_mul,mul_one,gram_p]
abbrev ruin (N:Side): Op (Single N):= spar 4 M (Ω N)* (1-PS N)
lemma ruination (p:TilePure (N:=N) M): ruin M N= Screen (wageErr N M):=by
 unfold ruin; rw [p]; have ha:1-PS N= Screen (1-P N):=by rw [upperP,tap_sub,show Screen (1:Op (SpinN N))=1 from Matrix.one_kronecker_one]; rfl
 rw [ha]; exact tap_times ..
lemma treasury (l:ℕ):∃ C:ℝ,0<C∧∀ N:Side,∀ (M:Tulip.Male)(u:Site N), TilePure (N:=N) M→∀ K:ℕ,0<K→ ‖ruin M N^(K*l)*hiveY M Z u (2*l+2)‖≤ C*((K:ℝ)⁻¹)^l:=by
 obtain ⟨C,h,p⟩:= trains Z l; exact ⟨C,h,fun N M u f K k=> (by rw [ruination M f,tap_self,hiveY, tap_times]; exact (tap_cost _).trans (p N u M K k))⟩
end YM.CF.Pannier.Chancel.Cuve
open YM.CF.Pannier.Chancel.Cuve
#print axioms ruination
#print axioms treasury
#print axioms hearty
#print axioms gramS
#print axioms spirit
