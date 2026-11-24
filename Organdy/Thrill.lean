import Organdy.Pavane
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.flexible false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Organdy
open Function Filter Topology Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet NormedSpace Scroll Finset Palot Cadre Vow
open RG Mew Rive Nor Hake MeasureTheory Bake Rue Salt
open Metric Drapes Tulip Lat Branch Cube Tenant
open Rush SU Prism Nacre Laic Tap Levier Thera Moto Oath Font Haro Spire Dial Rill
open Kennel
open Swell StressExchange Buffered
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra


open _root_.Zephyr.Chern
open Vale Py Py.Rate LocalLimit Preparation Buffered.Afterglow.Tower.VacuumSelection

variable {N:Side}
local notation "Ω"=> Single N


abbrev audible (s:Signed)(K:Scree.Loom N)(p:BudgetPoint)(X:SOp N):= chime K p (restL N s) (julStep (polestar N s) X)
lemma ebony_sq (s:Signed): ebony s * ebony s=1:=by unfold ebony; cases detX s <;> simp
lemma norm_ebony (s:Signed): ‖ebony s‖=1:=by unfold ebony; cases detX s <;> simp

/-- Rise of the chime of the Swept kernel; still have to apply
complex conjugation for improper s, which preserves rise. Includes
(unprojected) constant bound. -/
structure Audio (p:BudgetPoint)(a c δ:ℝ)(s:Signed)(g:Pane N→ℂ):Prop where
 scale: ‖g 1‖ ≤ c * Real.exp (-a*((p.B/10:ℕ):ℝ))
 pitch: Rising δ (fun t=>ebony s * g (petals (stream N) t))

variable (P:Spine)(i k t:ℕ)
local notation "Λ"=>P.par
local notation "N'"=> age P.run i t
local notation "d'"=> (Λ).d
local notation "πP" => PresN P i k t
variable {a b:ℝ} {m:ℕ}
lemma soldPiece {p:BudgetPoint}{K:Scree.Loom N'}{X Y:SOp N'}(r:Signed)
  (H:WindowDress K p d')
  (v:Trunk (node 0) X (p.B/10) a b d')
  (z:Soak (node 0) Y a (Real.exp (-a*((p.B/10:ℕ):ℝ))*b) d')
  (q:∀ w:Openc (More N') d',fullPay πP m w.val=X w.val+Y w.val)
  {W δ:ℝ}(u:Oily a d' 64 W)
  (g:Rising (2*δ) (dropArc (stream N') (cellPay πP (boughtTurn (polestar N' r) m))))
  (e:(W*Tenant.quota^2*b)*Real.exp (-a*((p.B/10:ℕ):ℝ))≤δ):
 Audio p a (W*Tenant.quota^2*b) δ r (audible r K p X):=by
 let s:=polestar N' r
 let A:=stream N'
 let T:=julStep s
 let M:=fullPay πP m
 let u':=W*Tenant.quota^2*b
 let tail:=Real.exp (-a*((p.B/10:ℕ):ℝ))
 have F: Lode A (T M) (audible r K p X) (T Y)
    u' (u'*tail):=by
     have w:=jul_trunk s v
     have t:=jul_sells s z
     have R:=rest_short (N:=N') r
     have h:∀ y: Openc (More N') d',(T M) y.val=(T X) y.val+(T Y) y.val:=by
        intro y; let x:= Sour.fog s d' y
        change ech _ (fullPay _ m x.val)=_
        rw [q x]; exact map_add (echoPlus _) _ _
     have l:=toned w t h H u (mildMore _ R)
     rw [show W*(Tenant.quota^2*(Real.exp _ * b))=u'*tail by unfold u' tail;ring,
       show W*(Tenant.quota^2*b)=u' by unfold u';ring] at l
     exact l
 refine ⟨?_,?_⟩
 · have z:(dropArc A (T M)) 0=0:=by
      unfold dropArc T julStep
      rw [petal_idle, ←Levier.veil_p,show stir _ _ (1:Pane N')=1 from flashes_clear s,ech_free, 
        show Matrix.trace (M (profile 1))=0 from lightFull_vanish ..]
      cases (s⁻¹).charge <;> simp [cSignX]
   change bud (dropArc A (T M)) 0=0 at z
   rw [F.sheer.bud_eq] at z
   change audible r K p X (petals A 0) + bud (dropArc A (T Y)) 0=0 at z
   rw [petal_idle] at z
   rw [eq_neg_of_add_eq_zero_left z,norm_neg]
   exact F.leftover 0
 let D := cellPay πP (boughtTurn s m)
 have w : dropArc A D =ᶠ[𝓝 0] (fun l=>ebony r*dropArc A (T M) l):=by
    filter_upwards [petals_safe A H.pos] with l h
    unfold dropArc T M fullPay
    rw [amberTip P i k t _ _ h,Matrix.trace_smul]
    change Matrix.trace _= ebony r*(ebony r*Matrix.trace (D _))
    rw [←mul_assoc,ebony_sq, one_mul]
 let B:=audible r K p X ∘ petals A
 let C:=dropArc A (T Y)
 have j:Bloom (dropArc A D) ((ebony r) • (bud B + bud C)) :=
   (F.sheer.scale _).congr w
 have r'':2*δ≤ (ebony r*bud B 2).re+(ebony r*bud C 2).re:=by
    have h:=g.price; change 2*δ≤(bud (dropArc A D) 2).re at h
    rwa [j.bud_eq,Pi.smul_apply,Pi.add_apply,smul_eq_mul,mul_add,Complex.add_re] at h
 have r': (ebony r*bud C 2).re≤δ:=by
    refine le_trans (Complex.re_le_norm _) ?_
    rw [norm_mul,norm_ebony,one_mul]
    exact (F.leftover _).trans e

 let f:=F.paid.bloom.scale (ebony r)
 refine ⟨f.1,?_⟩
 change δ≤(bud (fun x=> ebony r*(audible r K p X ∘ petals A) x) 2).re
 rw [f.bud_eq]
 change δ≤(ebony r*bud B 2).re
 linarith only [r'',r']

lemma soldAll (u:0<a)(v:0<b)(p':0 < m): ∃ c δ:ℝ, ∃ w:ℕ,
 0<c ∧ 0<δ ∧ ∀ᶠ t in atTop,∀ i k,
   ∀ (K:Scree.Loom (age P.run i t))(p:BudgetPoint) (X Y:SOp _),
   w ≤ p.B/10 →
   WindowDress K p d' →
   Trunk (node 0) X (p.B/10) a b d' →
   Soak (node 0) Y a (Real.exp (-a*((p.B/10:ℕ):ℝ))*b) d' →
   (∀ z:Openc (More (age P.run i t)) d',fullPay (PresN P i k t) m z.val=X z.val+Y z.val) →
   ∀ r,Audio p a c δ r (audible r K p X):=by
 obtain ⟨W,⟨U⟩⟩:= oily u (Λ).dpos 64
 obtain ⟨g,r,e⟩:=payRotated P m
 let δ:= ((2*m)^4:ℕ)*g/2
 let D:=W*Tenant.quota^2*b
 have Y:0<D:=mul_pos (mul_pos U.bound (pow_pos (show 0<Tenant.quota by linarith [quota_bound]) _)) v
 have G:0<δ:=by unfold δ; positivity
 obtain ⟨w,hw⟩:=exists_nat_gt (D/δ/a)
 refine ⟨D,δ,w,Y,G,?_⟩
 filter_upwards [e] with s h i k K p X Y' q f j l g' y
 set n:=((p.B/10:ℕ):ℝ)
 refine soldPiece P i k s y f j l g' U ?_ ?_
 · rw [show 2*δ=((2*m)^4:ℕ)*g by unfold δ;ring]
   exact h i k y
 have a0:D/δ/a < n:=hw.trans_le (Nat.cast_le.mpr q)

 have f1:= (div_lt_iff₀ G).mp ((div_lt_iff₀ u).mp a0)
 rw [neg_mul, Real.exp_neg,←div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]
 exact f1.le.trans (by
     rw [mul_comm _ δ,mul_comm n a]; exact mul_le_mul_of_nonneg_left ((le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp _)) G.le)
