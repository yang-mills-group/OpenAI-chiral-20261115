import GaugeFieldConstruction.Necromant
set_option autoImplicit false
noncomputable section
namespace YM.CF.Vale.Veins
open Function Filter Lattice Laurent Bloch Wilson Precision RG Next.Free Work.F08 Craft Pressure Stationary Tree Reef Hom AnalyticBridge.LocalGaussianLaws
open scoped Topology BigOperators ContDiff Matrix Matrix.Norms.Frobenius
open Exterior Next.Free.Stretch Finset Matrix
variable {L c f:Side}{C:ℝ}
open Crest.Shore CF.Jill CF.Fir
local notation "I"=>Complex.I
variable {α:Type*}{l:Filter α}{M:α→Side}{F:α→Momentum}(u:Tendsto M l atTop)(h:∀ᶠ i in l, Odd (M i).val){x:Bin}(v:Tendsto F l (𝓝 (tmap x)))
-- normalized lines. gauge ultimate
abbrev glowτ (a:ℝ):ℂ:=Complex.exp (I*(a:ℂ)/2)* Crest.skirt a
include u v
lemma narrowQ : Tendsto (fun i=>narrow (M i) (F i)) l (𝓝 0):=by simpa only [zero_smul,narrow] using (thinning u).smul v
private lemma meltF (z:Axis): Tendsto (fun i=> seedQ (M i) (F i) z) l (𝓝 (I*(x z:ℂ))):=by
 let G:= fun i=> narrow (M i) (F i) z
 have he:Tendsto (fun i=> dslope chip 0 (G i)) l (𝓝 I):=by
    have hp:HasDerivAt chip I 0:=by unfold chip; simpa using (((hasDerivAt_id' (0:ℂ)).const_mul I).cexp.sub_const (1:ℂ))
    rw [← hp.deriv, ← dslope_same]; exact (continuousAt_dslope_same.mpr hp.differentiableAt).tendsto.comp (tendsto_pi_nhds.mp (narrowQ u v) z)
 refine (he.mul (tendsto_pi_nhds.mp v z)).congr fun i=>?_; unfold seedQ; rw [show chip _=G i * dslope chip 0 (G i) from (by simpa only [sub_zero, chip_origin,smul_eq_mul] using (sub_smul_dslope chip 0 (G i)).symm)]; unfold G; rw [narrow_apply]; field_simp [side_ne ..]
lemma deltaQ : Tendsto (fun i=>divisor (M i) (F i)) l (𝓝 (↑(Crest.Shore.radius x):ℂ)):=by
 have hm:tmap (-x)= -(tmap x):=by funext i; unfold tmap; simp
 unfold divisor Crest.Shore.radius; push_cast; refine tendsto_finsetSum _ (fun i _=>?_)
 let he:= (meltF u v i).mul (meltF (M:=M) u (x:=-x) (by rw [hm]; exact v.neg) i) -- tune F'
 have hh:(I * (x i:ℂ))*(I*((-x) i:ℂ))=(x i:ℂ)^2:=by rw [Pi.neg_apply,Complex.ofReal_neg]; ring_nf; rw [Complex.I_sq]; ring
 exact hh ▸ he
include h
lemma tram (a:Axis): Tendsto (fun i=> rail (M i) ((narrow (M i) (F i)) a)) l (𝓝 (glowτ (x a))):=by
 let N(i):ℂ:= (M i).val
 have hp: Tendsto (fun i=> ((Next.Free.mid (M i)):ℂ)/N i) l (𝓝 (1/2)):=by
    have ht:Tendsto (fun i=>(1-(N i)⁻¹)/2) l (𝓝 (1/2)):=by simpa only [sub_zero] using (tendsto_const_nhds.sub (thinning u)).div_const 2
    refine ht.congr' ?_; filter_upwards [h] with i e; have he:2*((Next.Free.mid (M i)):ℂ)+1=N i:=by unfold N; exact_mod_cast mid_double (M i) e
    field_simp [show N i≠0 from side_ne (M i)]; linear_combination -he -- tune
 let g(i):= twirl ((narrow (M i) (F i)) a) (Next.Free.mid (M i)); have ht: Tendsto g l (𝓝 (Complex.exp (I*(x a:ℂ)/2))):=by
    have hh:=hp.mul ((tendsto_pi_nhds.mp v a).const_mul I); rw [show I * ↑(x a)/2=1/2*(I*tmap x a) by unfold tmap; ring]; apply ((Complex.continuous_exp.tendsto _).comp hh).congr; intro i; simp only [Function.comp_apply]; unfold g twirl N; rw [narrow_apply]; congr 1; ring
 have hy:= plank_c u (tendsto_pi_nhds.mp v a) h (x a) rfl
 refine (ht.mul hy).congr fun i=>?_; unfold g; rw [← narrow_apply _ (F i) a,Next.Free.plank, ← mul_assoc, ← twirl_add]; simp
variable (i j:Cover × PlaqAxes)(r:TypeFace 1)
abbrev Pontiff (b:Cover × PlaqAxes)(p:Bin)(r:TypeFace 1):ℂ:= (Crest.Shore.weave p)^4*glowτ (p (axisEquiv.symm r))*creditW b (tmap p) r
abbrev WritW (i j:Cover × PlaqAxes)(r:TypeFace 1)(p:Bin):ℂ:=(↑(Crest.Shore.radius p):ℂ)⁻¹ * (Pontiff j p r*star (Pontiff i p r))
abbrev chelate (p:Cover)(L:Side)(z:Momentum):ℂ:= if lift (wrap L p)=p then gateW i j z L (wrap L p) r else 0
lemma sweepsE(p:Bound Real.pi x)(b:x≠0)(w:Cover): Tendsto (fun k=> chelate i j r w (M k) (F k)) l (𝓝 (WritW i j r (x+ stem w))):=by
 let A:= x + stem w; let G(k:α):= F k+ reciprocal w
 have he:Tendsto G l (𝓝 (tmap A)):=by unfold A G; rw [map_stem]; exact v.add_const _
 have hN(k:α) : lift (wrap (M k) w)=w→ aliasAt (F k) (wrap (M k) w)=narrow (M k) (G k):=fun h=>by unfold aliasAt mon narrow G; rw [h,smul_add]
 have hz:0 < Crest.Shore.radius A:= Crest.Shore.radius_pos _ (norm_pos_iff.mp ((norm_pos_iff.mpr b).trans_le (peaks p (show peers x A from ⟨w,rfl⟩))))
 let K(k):=wrap (M k) w; have hd: Tendsto (fun k=> divisor (M k) ((M k).val • aliasAt (F k) (K k))) l (𝓝 (↑(Crest.Shore.radius A):ℂ)):=by
    apply (deltaQ u he).congr'; filter_upwards [u.eventually (raising w)] with k g; unfold K; rw [hN _ g]; unfold narrow; rw [← Nat.cast_smul_eq_nsmul ℂ,smul_inv_smul₀ (side_ne (M k))]
 have hh (z): Tendsto (fun k=> fenceW z (F k) (M k) (K k) r) l (𝓝 (Pontiff z A r)):=by
    have hk: creditW z (tmap x) r=creditW z (tmap A) r:=by unfold A; rw [map_stem,credit_phase]
    refine ((((decking u he h).mul (tram u h he _)).mul (hk ▸ ((resume z r).tendsto _|>.comp v)))).congr' ?_
    filter_upwards [u.eventually (raising w)] with k g; rw [receipts_B]; unfold K; rw [hN _ g]; rfl
 refine (((hd.inv₀ (by exact_mod_cast hz.ne')).mul ((hh j).mul ((hh i).star)))).congr' ?_; filter_upwards [u.eventually (raising w)] with k g; rw [chelate, if_pos g] <;> rfl
end YM.CF.Vale.Veins
end
