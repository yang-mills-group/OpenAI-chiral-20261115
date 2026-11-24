import Gingham.Ruff.Farina
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Gingham.Ruff
open Function NormedSpace Finset Fock Scree Pastry
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
open Lattice Wilson Laurent Cube SU Lat Spire Scroll Peaks Drapes Rush Precision Tulip Jet
    Tap Laic Dial Paige Vault Pec Skye Branch
variable {N:Side}
open Nacre Plumes

/-- Coif lying on physical slice. -/
structure Dyed(N:Side)(e:ℝ) where
 paneQ: Pane N
 live : Guard paneQ e
 openZ: 0<e
variable {e a c:ℝ}
namespace Dyed
def stack (x:Dyed N e):Coif N e := ⟨profile x.paneQ,⟨x.paneQ,x.live,by rw [sub_self,norm_zero];exact x.openZ⟩⟩
def actsD (d:Shape)(x:Dyed N e):Dyed N e :=
 ⟨Yg d x.paneQ, keepC inert d _ _ x.live, x.openZ⟩
lemma lace_stack (x:Dyed N e):lace x.stack=x.stack:=Subtype.ext (ice_pr _)
lemma aviator_stack (x:Dyed N e)(d:Shape):
 aviator d x.stack=(x.actsD d).stack:= Subtype.ext (perchProfile _ _)
end Dyed

variable {I:Type*}[Fintype I][DecidableEq I]
def siphon (b:Bool):Op I→+Op I :=
 if b then ⟨⟨star,star_zero ..⟩,star_add⟩ else .id _
@[simp] lemma siphon_no(q:Op I): siphon false q=q:=rfl
@[simp] lemma siphon_yes(q:Op I): siphon true q=star q:=rfl
lemma siphon_or(b:Bool)(q:Op I):
 siphon b q=if b then star q else q:=by cases b<;>rfl


variable (d:Shape)(U: UNI SpinIdx)(x:Dyed N e)
def plinth : OP N →+ OP N :=
 ((twist (owl N d U)).toRingEquiv.toAddEquiv.toAddMonoidHom).comp (siphon (detX d.s)) -- type?
lemma posed_stack (A:Fob N e):
    posed d U A x.stack=plinth (N:=N) d U (A (x.actsD d).stack):=by
  rw [posed,cope,x.aviator_stack]
  unfold plinth shift siphon
  by_cases t:detX d.s=true
  · rw [if_pos t,if_pos t,pointe,Dyed.lace_stack];rfl
  rw [if_neg t,if_neg t];rfl

lemma recoil (q:OP N):
 twist (owl N d U) (twist (prepU d U inert N) q) = q:=by rw [← twin,owl,inv_mul_cancel,twist_formula];simp




lemma recoil_plinth (q:OP N):
    plinth d U (twist (prepU d U inert N) (siphon (detX d.s) q))=q:=by
  change twist _ (siphon _ _) = _
  by_cases t:detX d.s=true
  · rw [t,siphon_yes,siphon_yes,←map_star,star_star,recoil]
  rw [Bool.eq_false_iff.mpr t,siphon_no,siphon_no,recoil]

variable (f g:Chin N → OP N)(u:Side)
abbrev slide (l:Cover) (i:Axis)(e:ℝ):Fob N e:=
 posed (lagX l) 1 (fun z=>bond f g u i 0 z.val)
abbrev crossbar (i:Axis)(l:Cover)(e:ℝ):=posed d U (slide f g u l i e)
abbrev baldaquin(e:ℝ):= posed d U (N:=N) (e:=e) (fun z=> yoke f u 0 z.val)
abbrev advancePlus(i:Axis):= hem i u.val
abbrev advanceNeg(i:Axis):= -advancePlus u i
def surplus (T:Axis → Cover → OP N):=
  ∑ i,(T i (advancePlus u i)-T i (advanceNeg u i))

lemma surplus_map (h:OP N →+ OP N)(T:Axis → Cover → OP N):
    surplus u (fun i w=> h (T i w))=h (surplus u T):=by rw [surplus,surplus,map_sum];simp_rw [map_sub]
def upshot(e:ℝ):Fob N e :=
 fun z=> surplus u (fun i l=>crossbar d U f g u i l e z)


variable {f g}(h:Plumes f g a c e)(j:JetS d.s false (detX d.s) U)

include h
lemma slide_val (l:Cover)(i:Axis):
    slide f g u l i e x.stack= bond f g u i (wrap N l) x.stack.val:=by
  rw [slide,posed_stack]
  change plinth _ _ (bond f g u i _ (profile (finery l x.paneQ)))=_
  rw [bond_lag h _ x.live, zero_add]
  change twist _ (siphon (detX 1) _)=_
  rw [det_i,siphon_no]
  exact recoil ..

lemma updraft :
    surplus u (fun i w=>slide f g u w i e x.stack)=oriole f g u 0 x.stack.val:= by
  unfold surplus
  rw [← cadenza f g]
  · exact sum_congr rfl fun i _=>by
       dsimp only
       rw [slide_val x u h,slide_val x u h,zero_add,zero_sub,advanceNeg,map_neg]; rfl
  exact h.pure _ x.live -- fix arguments binder order

include j
lemma breeze_T:
 oriole f g u 0 (x.actsD d).stack.val=
   twist (prepU d U inert N) (siphon (detX d.s) (oriole f g u (finale d 0) x.stack.val)):=by
  rw [siphon_or]; exact swan h _ x.live u 0 d U j


/-- (126) on dyed coefficients of full pushed charges. -/
theorem poise_J:
    upshot d U f g u e x.stack=oriole f g u (finale d 0) x.stack.val:=by
  simp only [upshot,crossbar,posed_stack d]
  rw [surplus_map,updraft _ _ h,breeze_T d U x u h j,recoil_plinth]

lemma fir_T:
    Matrix.trace (baldaquin d U f u e x.stack)=
     bust f u 0 (x.actsD d).stack.val:=by
  rw [baldaquin,posed_stack]
  change Matrix.trace (twist _ (siphon _ _))=_
  rw [twistTr,siphon_or]
  split
  · rw [star_trace, ← bust_yoke]
    exact lucid h _ (x.actsD d).live ..
  rfl

abbrev effect (d:Shape)(z:ℂ):= if detX d.s then -z else z
theorem poise_A:
    effect d (Matrix.trace (baldaquin d U f u e x.stack))=
    bust f u (finale d 0) x.stack.val:=by
  rw [fir_T d U x u h j]
  have ht:= signboard h x.paneQ x.live u 0 d false U j
  change effect d (bust f u 0 (profile (stir (xtra false) d x.paneQ)))=_
  rw [ht]
  simp only [effect]
  split <;> simp [Dyed.stack, *]


#print axioms poise_J
#print axioms poise_A
#print axioms framed_light
#print axioms pavilion

