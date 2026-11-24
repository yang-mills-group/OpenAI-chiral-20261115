import Anomaly.SprigLamp
import Anomaly.Weigh
import Zephyr.Bed
/-!
Top-form response on the MASKED & TRUNCATED probe, from the
per-site jet on the actual projector.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
noncomputable section
namespace Zephyr.Chern
open YM Lattice Filter Topology CF CF.Tulip CF.Cube CF.Lat
open CF.Tenant CF.Drapes CF.Branch Metric Finset
open scoped Matrix Matrix.Norms.L2Operator InnerProductSpace
attribute [local instance] opCStarAlgebra
open CF.Swell CF.Pastry CF.Scree CF.Skye CF.Fock CF.Sault CF.Rush
variable {N:Side}

lemma Bloom.minus {f g:ℝ→ℂ}{c d: Three ℂ}(h:Bloom f c)(w:Bloom g d):Bloom (fun x=>f x-g x) (c-d) := by
  simpa only [sub_eq_add_neg,neg_one_smul,neg_mul,one_mul] using h.add (w.scale (-1))

open CF.Py CF.Py.Rate CF.Py.Rate.LocalLimit CF.Py.Rate.LocalLimit.Preparation
open CF.Buffered.Afterglow.Tower.VacuumSelection
variable (P : Spine)
local notation "Nq" i:max s:max=> age P.run i s
local notation "Tq" i:max s:max=> petals (stream (age P.run i s))
local notation "Mq" i:max k:max s:max=> funde P.par.K.j (blood P.run i k s) (age P.run i s)

def fullSite (i k s:ℕ)(x:Site (age P.run i s))(t:ℝ) := siteRead x ((Mq i k s) (profile ((Tq i s) t))-Dial.tickA (Nq i s))

lemma site_reset (h:SprigFee P)(z:Cover) : ∃ δ :ℝ,0<δ∧∀ᶠ s:ℕ in atTop,∀ i k:ℕ, let f:=fullSite P i k s (wrap _ z); Bud f ∧ δ < (bud f 2).re := by
  obtain ⟨δ,v,T⟩:= h.actual z
  refine ⟨δ,v,T.mono fun s q i k => ?_⟩
  let x := wrap (Nq i s) z; intro f; let A:=Dial.tickA (Nq i s); let a:= siteRead x A
  have he : f=sparSite (N:=Nq i s) P.par.K.j (blood P.run i k s) z+Function.const _ (-a):=by
    funext t; unfold f fullSite sparSite; change (∑ u:SpinIdx,∑ v:SU.Slot, _)= (∑ y:SpinIdx×SU.Slot, _)+(-a)
    simp_rw [Matrix.sub_apply,sum_sub_distrib]; rw [Fintype.sum_prod_type,sub_eq_add_neg]; rfl
  rw [he]; exact q i k (-a)

-- Wind includes all the physical sites at the root. Map offsets on
-- the cover to ensure that even on changing tori these tests use fixed sites.
lemma bloomCube {m:ℕ} {f:Site N→ℝ→ℂ} {U : Finset ℕ} {c : ℕ → Three ℂ} {L: List Axis} (x:ℕ→Site N) (h:∀ i∈U,Bloom (fun t=>squareSum (fun y=>f y t) m L (x i)) (c i)) :
    Bloom (fun t=>∑ i∈U,squareSum (fun y=>f y t) m L (x i)) (∑ i∈U,c i) := Bloom.sum _ h

lemma cube_reset (h:SprigFee P)(m:ℕ)(w:1 ≤ m)(L:List Axis)(z:Cover) :
    ∃ δ : ℝ,0<δ∧∀ᶠ s:ℕ in atTop,∀ i k:ℕ, let f:=fun t=>squareSum (fun y=> fullSite P i k s y t) m L (wrap _ z); Bud f ∧ δ ≤ (bud f 2).re := by
  induction L generalizing z with
  | nil =>
    obtain ⟨δ,p,T⟩:=site_reset P h z; exact ⟨δ,p,T.mono fun s t i k => ⟨(t i k).1,(t i k).2.le⟩⟩
  | cons i L e=>
    let Z(c:ℕ): Cover:= z-m • step i+(c+1) • step i
    choose d hp ht using fun j=> e (Z j)
    let c:=range (2*m); have ho:0∈c:= mem_range.mpr (by omega)
    have hx:∀ᶠ s:ℕ in atTop,∀ j∈c,∀ x k, let f:=fun t=>squareSum (fun y=> fullSite P x k s y t) m L (wrap _ (Z j)); Bud f ∧ d j ≤ (bud f 2).re := eventually_all_finset c|>.2 fun j _=>ht j
    refine ⟨d 0,hp 0,hx.mono fun s t v k=>?_⟩
    intro f; let K(j:ℕ)(x:ℝ):ℂ:=squareSum (fun y=> fullSite P v k s y x) m L (wrap _ (Z j))
    have hF : Bloom f (∑ j∈c,bud (K j)):= by
      have hG : f=fun x=> ∑ j∈c, K j x :=by
        funext; simp only [f,squareSum, stripSum,K,moveSite,Z,map_sub,map_nsmul,map_add,wrap_step]; rfl
      rw [hG]
      exact bloomCube (f:=fullSite P v k s) (fun j=>wrap _ (Z j)) (fun j v=>(t j v _ k).1.bloom)
    refine ⟨hF.1,?_⟩
    rw [hF.bud_eq,Finset.sum_apply,Complex.re_sum]
    exact (single_le_sum (fun j _=>(hp j).le) ho).trans (sum_le_sum fun j q=>(t j q v k).2)

lemma tailDecay (a:ℝ)(p:0<a) : Tendsto (fun s:ℕ=> Real.exp (-a*((Pressure.radiusB (CF.Vale.hat P.par.R.L P.par.x s)/10:ℕ):ℝ))) atTop (𝓝 0) := by
  have he : Tendsto (fun s:ℕ=> Pressure.radiusB (CF.Vale.hat P.par.R.L P.par.x s)) atTop atTop:= Work.E01.radiusB_tendsto.comp (turnover P.par)
  exact Real.tendsto_exp_atBot.comp ((tendsto_natCast_atTop_atTop.comp ((Nat.tendsto_div_const_atTop (n:=10) (by omega)).comp he)).const_mul_atTop_of_neg (neg_lt_zero.mpr p))

-- closes λ germ for (133, right operand). Not (133)'s prices yet.
lemma aperture_field (h : SprigFee P)(a b : ℝ)(ha:0<a)(m:ℕ)(w:1 ≤ m) :
    ∃ δ : ℝ,0<δ ∧ ∀ᶠ s in atTop,∀ (i k:ℕ), s < P.run.uv k →
      ∀ J T: Axis→SOp (age P.run i s), ∀ X Z:SOp (age P.run i s),∀ f d : ℝ,
        CartPins P.run i k s m a b f d J T X Z →
          let F:=traceMeter (RootBook P.run i k s).p ((P.run.voyage i).CapeT s) 0 X
          Bud (F ∘ (petals (stream (age P.run i s)))) ∧ δ < (bud (F ∘ (petals (stream (age P.run i s)))) 2).re := by
  let Y:=P.run
  obtain ⟨δ,d,Hq⟩:= cube_reset P h m w (List.ofFn (id:Axis→Axis)) 0
  obtain ⟨W,⟨T'⟩⟩:= oily ha P.par.dpos 16
  let p:=fun s=>Y.meter.a s; let y(s:ℕ):=CF.Vale.hat P.par.R.L P.par.x s
  have ht : ∀ᶠ s:ℕ in atTop, W*(Real.exp (-a* ((Pressure.radiusB (y s)/10:ℕ):ℝ))*b) < δ/2:=
    (show Tendsto (fun s:ℕ=> W*(Real.exp (-a*((Pressure.radiusB (y s)/10:ℕ):ℝ))*b)) atTop (𝓝 0) from by simpa only [mul_zero,zero_mul] using (((tailDecay P a ha).mul_const b).const_mul W)).eventually (gt_mem_nhds (half_pos d))
  refine ⟨δ/2,half_pos d,?_⟩
  filter_upwards [Hq,ht] with s u t i k H J T X Z f d V F
  let R := RootBook P.run i k s; let K:= (P.run.voyage i).CapeT s
  have he:R.p=Y.meter.a s:= (((Y.voyage i).X (Y.uv k)).pull.owns s H.le).width.symm
  have gP:R.p.B= Pressure.radiusB (y s) := he.symm ▸ (Y.meter.boot s).2.1
  let N:=age P.run i s; let A:=stream N
  let g(t:ℝ): Pane N:= petals A t
  let E:=fun t=> Matrix.trace (((Mq i k s) (profile (g t))- Dial.tickA N)* windmill 0 m)
  have e:E=fun t=> squareSum (fun y=> fullSite P i k s y t) m (List.ofFn (id:Axis→Axis)) (wrap _ 0):=by funext; rw [map_zero]; exact wind_read _ _ _
  have hE: Bud E ∧ δ ≤ (bud E 2).re:=e ▸ (u i k) -- tune
  have l : Temper (node (0:Site N)) A 16:=by
    rw [show node (0:Site N)=1 by rw [node,map_zero,zero_add]]; exact stream_mild N
  obtain ⟨r,q⟩:= inTrace V.ropes.tubes.tailX T' l
  let X0:= traceJet Z A
  have hz: Bloom (F ∘ g) (bud E-bud X0) := by
    refine (Bloom.minus hE.1.bloom r.bloom).congr ?_
    refine (meter_pass 0 A (X:=X) V.pulse.roof V.pulse.reach).trans ?_
    filter_upwards [petals_safe A P.par.dpos] with v hv
    unfold E g traceJet; rw [V.ropes.tubes.readsX _ hv,Matrix.trace_add,add_sub_cancel_right]
  change Bud (F ∘ g) ∧ _ < (bud (F ∘ g) 2).re
  rw [hz.bud_eq,Pi.sub_apply,Complex.sub_re]
  refine ⟨hz.1,?_⟩
  have hb:(bud X0 2).re < δ/2 := (Complex.re_le_norm _).trans (q 2) |>.trans_lt (gP.symm ▸ t)
  linarith only [hb,hE.2]
end Zephyr.Chern
