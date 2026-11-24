import Gingham.Ruff.Kilt
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
open Nacre

/-- Second gauge-aligned coordinate centers: block center even, mode nodes odd. -/
def bouton (y:Site N):Seat N:=(assembly N).embed y

lemma bouton_clear (y:Site N): separation (bouton y) (node y) ≤ 1:=by
  rw [separation_comm,Lattice.separation]
  rw [show node y=bouton y+1 from rfl,add_sub_cancel_left]
  have h: (1:Seat N)=wrap (More N) 1:=by funext i; change (1:Per (More N))=((1:ℤ):Per (More N));simp
  rw [h];apply Work.E01.pdist_wrap_le
  simp

lemma bouton_finale (d:Shape)(y:Site N):
  bouton (finale d y)= d.anon N (bouton y):=by
  unfold bouton finale Shape.anon Lattice.affine
  rw [← Ratio.root_embed,map_add, Ratio.root_embed, Ratio.root_embed, Ratio.signed,Ratio.embed_wrap];rfl

/-! Gathering maps. -/
variable {e a c:ℝ}{A:Fob N e} (d:Shape)(U: UNI SpinIdx)

def shift (b:Bool)(A:Fob N e):Fob N e:=if b then pointe A else A
def posed (A:Fob N e):Fob N e:= cope d U (shift (detX d.s) A)

def widthL(u:Side):=1+2*(u.val+1)
def Girder (y:Site N)(u:Side):=faerie (Tenant.terr (More N)) (bouton y) (widthL u) 5
abbrev Plastron (y:Site N)(u:Side)(e:ℝ):= Buttons N e (Girder y u)


def Alter {R Q:Seal (Seat N)→Prop}(H:Buttons N e R a c A)
    (h:∀S, R S→Q S):Buttons N e Q a c A:={H with good:=fun _ i j t=> h _ (H.good _ i j t)}
def Top {R:Seal (Seat N)→Prop}(H:Buttons N e R a c A){b:ℝ}(h:c≤b):Buttons N e R a b A:={H with paid:=H.paid.trans h}
lemma Alter_light {R Q:Seal (Seat N)→Prop}(H:Buttons N e R a c A)(m:ℕ)
    (h:∀S, R S→Q S): (Alter H h).light m=H.light m:=rfl

variable {y:Site N}{u:Side}(H:Plastron y u e a c A)
def mist:∀ (b:Bool),Plastron y u e a c (shift b A)
 | true=>arabesque H
 | false=>H
lemma mist_light (b:Bool)(m:ℕ): (mist H b).light m=shift b (H.light m):=by
 cases b
 · rfl
 exact arabesque_light H m

def framed :
   Plastron (finale d y) u e a (tableland^2*c) (posed d U A):=
   Alter (wig d U (mist H _))
     (fun S v=>by
       unfold Girder;rw [bouton_finale]; exact wig_norm _ _ v)
lemma framed_light (m:ℕ): (framed d U H).light m= posed d U (H.light m):=by
  exact (wig_light d U (mist H _) m).trans (congrArg (cope d U) (mist_light H _ m))



def nectar (u:Side)(a c:ℝ):=
 (c * Real.exp ((a/20)*(widthL u:ℝ))) *
   (Tenant.quota*primaries 4 (a/20))

lemma garner (ha:0<a){f:Chin N→OP N}(h:Garland y u (a/2) c f e):
    Nonempty (Plastron y u e (a/4) (nectar u a c) (fun p=>f p.val)):=by
  have hp: Jabot (Girder y u) (a/2) c f e:= h.shape (fun S _ _ _ _ _ b z hz=>by
     have t:=separation_triangle (bouton y) (node y) z
     have hq:separation (node y) z ≤ 2*(u.val+1)+5*S.card:= b _ hz
     change separation (bouton y) z ≤ _
     unfold widthL; have := bouton_clear y; omega)
  exact hp.cashed (d:=a/20) (meterQ ..) ((show (0:ℝ)≤16 from by norm_num).trans Tenant.quota_bound)
     (by positivity) (by norm_num;linarith)

abbrev Pep (N:Side)(u:Side)(a c:ℝ)(e:ℝ):= Plastron (0:Site N) u e (a/4)
  (nectar u a (seamMoney u ((c+wingRent Fir.Aop a)+aviary a c)))
structure GarlandBook {N:Side}(u:Side)(a c e:ℝ)(f g:Chin N→OP N) where
  pump: Pep N u a c e (fun z=>yoke f u 0 z.val)
  point(i:Axis): Pep N u a c e (fun z=>bond f g u i 0 z.val)


variable {f g:Chin N→OP N}

lemma pavilion (ha:0<a)(h:Plumes f g a c e)(u:Side):
    Nonempty (GarlandBook u a c e f g):=by
  have p:= (feathers1 0 h.lead).positive
  have g₁:=(show Dahlia 0 0 5 _ _ _ _ from moorhen ha h.lead h.silk 0 0).positive
  have v(r s:ℝ)(e:r≤ s):seamMoney u r≤ seamMoney u s:=by
    exact mul_le_mul_of_nonneg_left e (Nat.cast_nonneg _)
  exact ⟨Classical.choice (garner ha
     ((patron u 0 ha.le h.lead).books (v _ _ (le_add_of_nonneg_right g₁)))),
     fun i=> Classical.choice (garner ha
     ((courier u 0 i ha h.lead h.silk).books (v _ _ (le_add_of_nonneg_left p))))⟩

