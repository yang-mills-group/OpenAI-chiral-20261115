import YM.CF.Rel.Coupe
set_option autoImplicit false
noncomputable section
namespace YM.CF.Rel
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch MeasureTheory NormedSpace Nacre Braid Font
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable{G:Gauge}{n:Side}{m l r:ℕ}{A C σ:ℝ}
open Stationary Push.Loops
open Cube
variable {F:FileM (More n) G}(p:LayerP n F){Z:G.Color→ₗᵢ[ℝ]G.Color}
def Head(n:Side)(C:G.Color→ₗᵢ[ℝ] G.Color)(F: FileM n G):Prop:=
 (∀ i, ∀ᶠ u in 𝓝 (0:InputZ G n),satX (F i) (Vsail C u)=star (satX (F i) u)) ∧ ∀ i s,∀ᶠ u in 𝓝 (0:InputZ G n), F i (pull (Signed.mirror s) 0 (represent u))=star (satX (F ((Signed.mirror s).act i)) u)
private lemma calm(x:Site n):Tendsto (fun z:InputZ G n=> te z x) (𝓝 0) (𝓝 0):=by have ht:=(tagT G x).continuous.tendsto 0; rw [map_zero] at ht; exact ht
private lemma crept (s:Signed)(v: InputZ G n)(x:Site n): Lattice.translate x (pull s 0 (represent v))=pull s 0 (represent (te v (s.act x))):=by rw [trn,← Lattice.pull_one,← Lattice.pull_one,Lattice.pull_pull,Lattice.pull_pull]; simp [affine]
include p
lemma hatch(q:Head (More n) Z F): Twice Z (laidC 0 n F 0):=by
 let T:=fun i:Charm=>F (logo n i) ∘ Lattice.translate (-logo n i)
 have hx:laidC 0 n F 0=massX⁻¹ • ∑ i:Charm,T i:=by change stroll _ 0 _ = _; rw [stroll_z]; unfold reel; simp_rw [show ∀ i:Charm, cell 0 i =1 from fun i=> (cell_duality ..).trans (cell_origin _),one_smul]; rfl
 have hm : star massX⁻¹=massX⁻¹:=by simp [massX]
 rw [hx]; constructor
 · have hv(i:Charm): ∀ᶠ u:InputZ G (More n) in 𝓝 0, satX (T i) (Vsail Z u)=star (satX (T i) u):=by
      filter_upwards [(calm (-logo n i)).eventually (q.1 (logo n i))] with y hy; unfold satX T; simp only [Function.comp_apply]; rw [←trn,←trn]; exact hy
   filter_upwards [eventually_all.mpr hv] with y hy; unfold satX; simp only [Function.comp_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul,star_mul, hm, star_sum]; rw [mul_comm]; -- tune
   congr 1; exact sum_congr rfl fun i _=> hy i
 intro i; let a:=Signed.mirror i; have he(k:Charm): ∀ᶠ u:InputZ G (More n) in 𝓝 0,(T k) (pull a 0 (represent u))=star ((T (a.act k)) (represent u)):=by
    let K:= logo n k
    filter_upwards [(calm (a.act (-K))).eventually (q.2 K i)] with u hu
    let W:=represent u
    have hp : logo n (a.act k)= logo n ((assembly n).residue (a.act K)):=by rw [show a.act K= wrap _ (a.act (lift k)) from wrap_signed ..,Ratio.residue_wrap]; change _=logo n (wrap 2 _); rw [←wrap_signed,wrap_lift]
    unfold T; change F K (Lattice.translate (-K) _)=star (_); rw [hp,← pose_t p]; unfold K at *; simp only [Function.comp_apply, crept]; rw [show -(a.act (logo n k))=a.act (-logo n k) from (Signed.act_neg ..).symm,← trn]; exact hu -- tune
 filter_upwards [eventually_all.mpr he] with y hy
 unfold satX; simp only [Function.comp_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul,star_mul,star_sum,hm]; rw [mul_comm]; congr 1; change ∑ k,T k (pull a 0 (represent y))=∑ k,star (T k _); simp_rw [hy]; exact Equiv.sum_comp (Signed.actEquiv (R:= Per 2) a).toEquiv (fun k=>star (T k (represent y))) -- tune
omit p in
lemma φ_pos(k:Charm)(p: k≠0): ∃ i:Axis, Exterior.q (axes (phi k)) i ≠0:=by
 obtain ⟨i,hx⟩:=step_picks k p; refine ⟨i,?_⟩; intro he; change Complex.exp _-1=0 at he
 have hp:= (fitP 1 k).step i; rw [←hp] at he; rw [gamma_pay (n:=1),←wrap_step,Ratio.residue_wrap] at he; change cell k (wrap 2 (Lattice.step i)) -1=0 at he; rw [wrap_step] at he; exact hx (sub_eq_zero.mp he) -- invalid final False implicit
end YM.CF.Rel
