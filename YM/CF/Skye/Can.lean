import YM.CF.Spire.Sum
import YM.CF.Reef.Pole
import YM.CF.Mesa.Hacienda
import YM.Work.H03
set_option autoImplicit false
noncomputable section
namespace YM.CF.Skye
open Function Filter Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.Frobenius
variable {n:Side}
abbrev Pane(n:Side):= Config group (More n)
abbrev Seat(n:Side):=Site (More n)
def boxA(s:Sweep n):Seat n ≃ Seat n where
 toFun:=(castX s).anon n
 invFun:=(castX s⁻¹).anon n
 left_inv x:=by rw [stirP,inv_mul_cancel,stir_l]; change affine 1 ((assembly n).root 0) _=_; rw [map_zero]; simp [affine]
 right_inv x:=by rw [stirP,mul_inv_cancel,stir_l]; change affine 1 ((assembly n).root 0) _=_; rw [map_zero]; simp [affine]
lemma sitA(s:Sweep n)(x):boxA s x=affine s.s ((assembly n).embed s.b) x:=stir_l s x
lemma sitT(s:Sweep n)(x y):separation (boxA s x) (boxA s y)=separation x y:=by simp [sitA,affine]
lemma sitU(s:Sweep n):boxA s⁻¹=(boxA s).symm:=by ext x; rfl
lemma sitV(s t:Sweep n)(x):boxA s (boxA t x)=boxA (s*t) x:=stirP ..
lemma revoke (s: Sweep n)(V: Pane n): flashA s V=polarT s.charge ∘ pull s.s ((assembly n).embed s.b) V:=by
 unfold flashA stir xtra; rw [show wrap (More n) (2 • (castX s).t) = _ from (Ratio.embed_wrap (assembly n) (Lattice.lift s.b)).symm,wrap_lift]; rfl
lemma rev1(V:Pane n):flashA 1 V=V:=by rw [revoke]; change polarT false ∘ pull 1 ((assembly n).root 0) V=V; rw [map_zero,pull_id]; rfl
lemma revB(s:Sweep n)(V:Pane n):flashA s⁻¹ (flashA s V)=V:=by rw [lights,mul_inv_cancel,rev1]
lemma rev_C(b:Bool): Continuous (polarT b):=by cases b; exact continuous_id; exact Reef.icyC
lemma revM(s:Sweep n):Continuous (flashA s):=by
 have hx:flashA s=(fun V=>polarT s.charge ∘ pull s.s ((assembly n).embed s.b) V):=funext (revoke s); rw [hx]; apply continuous_pi; intro i; exact (rev_C _).comp ((continuous_apply i).comp (continuous_pull s.s ((assembly n).embed s.b)))
lemma revG(s:Sweep n)(V:Pane n)(f:Seat n→E): flashA s (gauge f V)=gauge (fun i=>polarT s.charge (f (boxA s i))) (flashA s V):= (siren s.charge (castX s) n V (fun _=>Classical.arbitrary _) f).1 -- tune
lemma flagsQ{N:Side}(b:Bool)(V: Config group N)(u:ℝ): RG.flags u (polarT b ∘ V)=RG.flags u V:=by
 cases b; rfl
 change RG.flags u (Reef.echo V)=_; ext i; simp only [RG.flags_spec,faceValue,Reef.echo_t, Reef.cool]
lemma flagsA(s:Sweep n)(V:Pane n)(u:ℝ): RG.flags u (flashA s V)=(RG.flags u V).map (boxA s).symm.toEmbedding:=by
 rw [revoke,flagsQ]; set X:=RG.flags u (pull s.s ((assembly n).embed s.b) V); nth_rw 1 [← Work.H03.flags_send s.s ((assembly n).embed s.b) u V] -- tune
 rw [show X.image _ = X.map (boxA s).toEmbedding from ?_, Finset.map_map]; · ext; simp
 rw [map_eq_image]; rfl -- sit
lemma chair(s:Sweep n)(u:ℝ)(V:Pane n)(x): x∈RG.flags u (flashA s V) ↔ boxA s x∈RG.flags u V:=by rw [flagsA]; simp
abbrev ends(i:Edge (Site n)) :Finset (Site n):= {i.1,i.1+step i.2}
abbrev lane(s:Sweep n)(i:Edge (Seat n)) : Edge (Seat n):= sendEdge s.s ((assembly n).embed s.b) i
lemma flash(s:Sweep n)(V:Pane n)(e:Edge (Seat n)): flashA s V e=polarT s.charge (if s.s.flip e.2 then (V (lane s e))⁻¹ else V (lane s e)):=by rw [revoke]; cases h:s.s.flip e.2<;> simp [Lattice.pull,h,lane,sendEdge,Step.used,Step.read,Step.rotate,posDir]
lemma laneX(s:Sweep n)(e:Edge (Seat n)):ends (lane s e) = (ends e).map (boxA s).toEmbedding:=by
 have ht:= salt (N:=n) (castX s) (posDir e.2) e.1; change boxA s (e.1+step e.2)=boxA s e.1+_ at ht; rw [ends,ends,map_insert,map_singleton]; simp only [Equiv.toEmbedding_apply,ht,sitA]
 cases h:s.s.flip e.2 <;> simp [lane,sendEdge,Step.used,h, Step.rotate,posDir,castX,Step.vec]
 rw [Finset.pair_comm, ← sub_eq_add_neg]
lemma flashD (s:Sweep n)(V W:Pane n)(S: Support (More n))(h:Agrees (S.map (boxA s).toEmbedding) V W): Agrees S (flashA s V) (flashA s W):=by
 intro i hi hy; rw [flash,flash]; have ht:ends i⊆ S:=by simp only [ends,insert_subset_iff, singleton_subset_iff]; exact ⟨hi,hy⟩
 have hu: ends (lane s i) ⊆ _:=(laneX s i).symm ▸ (Finset.map_subset_map.mpr ht : _ ⊆ S.map (boxA s).toEmbedding); rw [h (lane s i) (hu (by simp)) (hu (by simp))]
lemma paysT(s:Sweep n)(Y:Support (More n))(B:ℕ) : halo B (Y.map (boxA s).toEmbedding)=(halo B Y).map (boxA s).toEmbedding:=by ext i; obtain ⟨i,rfl⟩:= (boxA s).surjective i; simp [halo_spec]; constructor; rintro ⟨y,u,h⟩; obtain ⟨z,rfl⟩ := (boxA s).surjective y; exact ⟨z, by simpa using u, sitT s z i ▸ h⟩; rintro ⟨y,u,h⟩; exact ⟨_,(by rw [Equiv.symm_apply_apply]; exact u), (sitT s y i).symm ▸ h⟩
end YM.CF.Skye
