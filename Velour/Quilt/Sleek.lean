import Velour.Quilt.Cash

/-! # Velvet pays for jets
-/
set_option autoImplicit false
set_option maxHeartbeats 950000
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
namespace Spine
open Aria Casting Six OS.Semigroup.Balloon



open MacroGrid SatinNucleus Velour

open SatinJets OS.Semigroup
variable (P:Spine)(x:P.Spectrum0 3)
local notation "K"=>P.calibration
local notation "θ₀"=> (3:Axis)
local notation "𝒞"=> P.ColorHil θ₀ x
local notation "σ"=> P.physicalEnergy θ₀ x
local notation "τ"=>P.macroStep
local notation "m"=> timeMesh P.par
local notation "κ"=> P.shifts θ₀
local notation "β"=> bell (timeMesh P.par)

abbrev readyDye (T:ℕ→P.Apron)(Y:ℝ→(𝒞).Op):Prop:=
   Tendsto (fun i=>(T i).realWidth P θ₀) atTop (𝓝 0)
     ∧ Pays (𝒞) τ (fun t i=> (T i).velour P θ₀ x t) Y

variable {P x}{T D:ℕ→P.Apron}{Y:ℝ→(P.ColorHil 3 x).Op}

lemma Veloured.seen(h:P.Veloured θ₀ x T): P.readyDye x T h.printOp:=
  ⟨h.thin,fun _=>h.printed,h.bill⟩
namespace readyDye

lemma gets (h:P.readyDye x T Y):P.Veloured θ₀ x T:=
  ⟨h.1,fun d e=>⟨_,h.2.see d e⟩,h.2.bill⟩

lemma dyes (h:P.readyDye x T Y){t:ℝ}(e:0<t):
    h.gets.printOp t=Y t:=(h.gets.printed e).unique (h.2.see t e)

lemma meshThin (h:P.readyDye x T Y):Tendsto (fun i=>τ (T i).s) atTop (𝓝 0):=by
 refine squeeze_zero (fun i=> (P.macroStep_pos _).le) (fun i=>?_) h.1
 unfold macroStep Apron.realWidth bell
 refine le_mul_of_one_le_left (P.macroStep_pos _|>.le) ?_
 exact_mod_cast Nat.succ_le_iff.mpr ((T i).pos θ₀)


lemma grounds (h:P.readyDye x T Y){a b:ℝ→ℕ→ℝ}{d:ℝ→ℝ}
    (g:∀ t:ℝ,0<t→t/2<d t ∧ Tendsto (a t) atTop (𝓝 (d t)) ∧ Tendsto (b t) atTop (𝓝 (d t))):
   Pays (𝒞) τ (fun t i=> (T i).dye P θ₀ x (a t i) (b t i)) (fun t=>Y (d t)):=by
 obtain ⟨B,L,p,q,u⟩:= h.gets.rich
 refine ⟨fun t w=>?_, B,L,p,q,u.mono fun k c=>?_⟩
 · obtain ⟨r,y,z⟩:=g t w
   have t':0<d t:=(half_pos w).trans r
   rw [← h.dyes t']
   exact h.gets.wvary t' y z
 obtain ⟨r,y,z⟩:=g (τ k) (P.macroStep_pos _)
 filter_upwards [c,y.eventually (le_mem_nhds r),z.eventually (le_mem_nhds r)] with i d' i' j'
 exact d' _ i' _ j'
lemma quiltPays (h:P.readyDye x T Y):
    Pays (𝒞) τ (quilt (σ) (fun i=>whenly m (T i).s 1)
       (fun d i=> (T i).dye P θ₀ x (d-d/4) (d-d/4- τ (T i).s)))
       (piping (σ) Y):=by
 refine pipingPays (σ) τ _ ?_ ?_ P.macroStep_pos
     (L:=(P.par.R.L.val:ℝ)) ?_ ?_ ?_


 · exact NNReal.tendsto_coe.mp (h.meshThin.congr fun _=>(P.quilt_speed ..).symm)
 · intro i; rw [←NNReal.coe_pos, P.quilt_speed]; exact P.macroStep_pos _
 · have h':1≤P.par.R.L.val:=by have :=P.par.V.tallX; omega
   exact_mod_cast h'
 · intro k; simpa only [Nat.sub_zero] using P.daysF k 0 (Nat.zero_le _)
 refine h.grounds fun t p=> ⟨by linarith, tendsto_const_nhds,?_⟩
 simpa using (tendsto_const_nhds (x:=t-t/4)).sub h.meshThin

-- formal stencil stepped once
lemma cash (h:P.readyDye x T Y)
    (a:∀i,(D i).s=(T i).s)
    (b:∀i,(D i).realWidth P θ₀=(T i).realWidth P θ₀ + τ (T i).s)
    (v:∀i,(D i).F=(duration (whenly m (T i).s 1))⁻¹ • (κ 1 (T i).F - (T i).F)):
    P.readyDye x D (piping (σ) Y):=by
 have ht:Tendsto (fun i=>(D i).realWidth P θ₀) atTop (𝓝 0):=by
    simp_rw [b]; exact zero_add (0:ℝ) ▸ h.1.add h.meshThin
 refine ⟨ht,h.quiltPays.agree P.macroStep_pos (fun t p=>?_ ) fun _ _=>rfl⟩
 have z:0<t-t/4:=by linarith
 filter_upwards [ht.eventually_le_const z] with i u
 have y:=u
 rw [b] at y
 exact (P.knit_price x (T i) p y).trans (P.quilt_price x (T i) (D i)
     (a i) (b i).ge (v i) (by linarith)).symm


-- sum fixed order
lemma plush {ι:Type*}{s:Finset ι}{Q:ι→ℕ→P.Apron}{U:ι→ℝ→(𝒞).Op}
   (z:ι→ℂ)(u:∀j∈s,P.readyDye x (Q j) (U j))
   (ht:Tendsto (fun i=> (D i).realWidth P θ₀) atTop (𝓝 0))
   (b:∀i,∀j∈s,(Q j i).s=(D i).s ∧ (Q j i).realWidth P θ₀+τ (D i).s≤(D i).realWidth P θ₀)
   (r:∀i,(D i).F=κ 1 (∑j∈s,z j • (Q j i).F)):
   P.readyDye x D (fun t=>∑j∈s,z j • U j t):=by
 have e(j:ι)(a:j∈s): Tendsto (fun i=>τ (D i).s) atTop (𝓝 0):=
   (u j a).meshThin.congr fun i=>congrArg _ (b i j a).1
 have hh (j:ι)(a:j∈s):
     Pays (𝒞) τ (fun t i=> (Q j i).dye P θ₀ x (t+τ (D i).s) (t-τ (D i).s)) (U j):= by
        refine (u j a).grounds (d:=fun t=>t) fun t h=> ⟨half_lt_self h,?_,?_⟩
        · simpa using (e j a).const_add t
        simpa using (tendsto_const_nhds (x:=t)).sub (e j a)


 refine ⟨ht,(Pays.sum s fun j a=>(hh j a).smul (z j)).agree P.macroStep_pos ?_ fun t _=>rfl⟩
 intro t q; filter_upwards [ht.eventually_le_const q] with i t'
 exact (P.plush_price x (D i) (fun j=>Q j i) z s (b i) (r i) t').symm

end readyDye

variable (P x)

-- true Aprons at intermediate orders
def textured (Q:P.Apron) (n:ℕ) : P.Apron where
 s:=Q.s
 u:=fun j=>Q.u j+n
 F:=P.tubaField Q.s Q.F n
 S:=P.tubaStencil Q.S n
 realM:=P.tuba_real _ _ _ Q.realM
 pos:=fun j=>Nat.add_pos_left (Q.pos j) _
 shelter:= fun j=> P.tubaShelter j (Q.shelter j) n
 bay:=P.tuba_bay _ _ _ _ Q.bay

lemma texture_width (j:Axis)(Q:P.Apron) (n:ℕ):
    (P.textured Q n).realWidth P j = Q.realWidth P j + n*τ Q.s:=by
 unfold Apron.realWidth
 simp only [textured,Nat.cast_add,bell,Int.cast_add,add_mul,Int.cast_natCast]
 <;> try rfl

variable {P x}
lemma readyDye.textures (h:P.readyDye x T Y)(n:ℕ):
    P.readyDye x (fun i=>P.textured (T i) n) ((piping (σ))^[n] Y):=by
 induction n with
 | zero=>exact h
 | succ n ih=>
   rw [Function.iterate_succ_apply']
   refine ih.cash (fun _=>rfl) ?_ (fun _=>rfl)
   intro i
   rw [P.texture_width,P.texture_width]
   change _ = _ + τ (T i).s
   push_cast; ring


lemma readyDye.crop (h:P.readyDye x T Y)(W:Prism):
   P.readyDye x (fun i=>P.aTuba W (T i)) (trims (σ) W Y):=by
 refine readyDye.plush (Q:=fun j i=>P.textured (T i) (j+1)) W (fun j _=>h.textures (j+1)) ?_ (fun i j y=>⟨rfl,?_⟩) (fun _=>rfl)
 · simp_rw [P.tuba_width]
   simpa only [mul_zero,add_zero] using h.1.add
            (h.meshThin.const_mul (((lastTuba W+1:ℕ):ℝ)))
 rw [P.texture_width,P.tuba_width]
 have e:(j+1:ℕ) ≤ lastTuba W:= Finset.le_sup (f:=fun i=>i+1) y
 have r:(j+1:ℝ) ≤ lastTuba W:=by exact_mod_cast e
 simp only [aTuba]
 push_cast at * -- only
 linarith only [mul_le_mul_of_nonneg_right r (P.macroStep_pos (T i).s|>.le)]

lemma Veloured.trumpet (h:P.Veloured θ₀ x T)(W:Prism):
    P.Veloured θ₀ x (fun i=>P.aTuba W (T i)):= (h.seen.crop W).gets
lemma Veloured.trumpet_print (h:P.Veloured θ₀ x T)(W:Prism){t:ℝ}(p:0<t):
    (h.trumpet W).printOp t=trims (σ) W h.printOp t:=(h.seen.crop W).dyes p


#print axioms Veloured.trumpet_print
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
