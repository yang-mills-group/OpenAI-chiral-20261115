import YM.CF.Buffered.Oblique
import YM.CF.Buffered.Diphthong
/-!
# Buffered interiors inside tile copies. Note pad measured in gauge coordinates.
-/
set_option autoImplicit false
set_option maxHeartbeats 480000
set_option synthInstance.maxSize 18000
noncomputable section
namespace YM.CF.Buffered
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory Fock Gloss Scroll Spire Push.SectorMeasure
open Tree Heat Advance Stencil Branch Wilson Rush Peaks Scroll Phase Skye Pastry Tulip Dial Paige Scree RG Vault Fir Next.SectorChange Girt Region Roost Ordered Vale Crust Grid
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
attribute [local instance] opCStarAlgebra
namespace Solid
variable {N P D:Side}{e R u w:ℕ}(K:Planck N P D) (r:Tower D)
-- Cover presentation for each. Proof mirrored from band locals.
-- symmetric CLOSED core, use with POSITIVE e so inside open high Post.
def Damp (P:Side)(e:ℕ)(z:Cover): Prop := ∀ i:Axis,(e:ℤ) ≤ z i ∧ z i+(e:ℤ) ≤ P.val
def wallZ (K:Planck N P D)(r: Tower D) (e:ℕ): Support N :=by classical exact univ.filter fun x=> ∃ z:Cover, Damp P e z ∧ x=K.zone r z
lemma seam (e:ℕ)(x:Site N) : x∈wallZ K r e ↔ ∃ z:Cover,Damp P e z ∧ x=K.zone r z:=by classical simp [wallZ]
lemma monotoneV (t:u≤e): wallZ K r e ⊆ wallZ K r u :=by intro x hx; obtain ⟨z,v,p⟩:=(seam ..).1 hx; exact (seam ..).2 ⟨z,fun i=>by specialize v i; omega,p⟩
lemma up_ledge (g:R < e)(x:Site N)(hx:x∈wallZ K r e) (z:Site N)(v:separation z x ≤ R) : ledge K z=r:= by
 obtain ⟨y,b,w⟩:= (seam ..).1 hx; let d:=wrap P y
 have he:natural d=y:=by
    funext i; specialize b i; unfold natural d; rw [wrap_here,int_val _ (by omega) (by omega),Int.toNat_of_nonneg (by omega)]
 apply ledge_v K r d (show Deep P d R from fun i=>by rw [he]; specialize b i; omega) z; rw [toe,he]; exact w ▸ v
lemma keep (g:0<e)(x:Site N)(h:x∈wallZ K r e) : ledge K x=r:= up_ledge K r g x h x (separation_self _).le
lemma solid_pad (p:u+R ≤ e) : halo R (wallZ K r e) ⊆ wallZ K r u:=by
 intro x h; obtain ⟨y,v,k⟩:= halo_spec.mp h; obtain ⟨t,b,rfl⟩:=(seam ..).1 v; let a:= lift (x-K.zone r t)
 apply (seam ..).2; refine ⟨t+a,fun i=> ?_,?_⟩
 · rw [Pi.add_apply]; have he:(a i).natAbs ≤ R:= (component_le ..).trans ((separation_comm x _).trans_le k); specialize b i; omega
 rw [Planck.zone_add,show wrap N a=x-K.zone r t from wrap_lift .., add_sub_cancel]
lemma far_off {t:Tower D}{x y:Site N} (b:R < e)(p:x∈wallZ K r e)(q:y∈wallZ K t e)(h:r≠t) : R < separation x y :=by
 by_contra! g; exact h ((up_ledge K r b x p y ((separation_comm _ _).trans_le g)).symm.trans (keep K t ((Nat.zero_le _).trans_lt b) y q))
lemma broadens {n m l v:Side} (K:Planck (More n) (More l) D)(H:Planck (More m) (More v) D)(G:Ratio n m)(p:(More v).val=(More l).val*G.count.val)(r:Tower D) (z:Cover): (ratio G).embed (K.zone r z)=H.zone r (G.count.val • z):=by
 unfold Planck.zone; rw [Ratio.embed_wrap,smul_add]; congr 2
 change G.count.val • K.sail r=H.sail r; funext i; simp only [Planck.sail,Pi.smul_apply,nsmul_eq_mul]; rw [p]; push_cast; ring
lemma swell {n m l v:Side} (K:Planck (More n) (More l) D)(H:Planck (More m) (More v) D)(G:Ratio n m)(p:(More v).val=(More l).val*G.count.val)(r:Tower D) {x:Seat n}(h:x∈wallZ K r e): (ratio G).embed x∈wallZ H r (G.count.val*e):=by
 obtain ⟨z,v',rfl⟩:= (seam ..).1 h; apply (seam ..).2; refine ⟨G.count.val • z,fun i=>?_,broadens K H G p r z⟩
 rw [Pi.smul_apply,nsmul_eq_mul]; have he:0<G.count.val:= G.count.property; specialize v' i; rw [p]; simp only [Nat.cast_mul]; constructor <;> nlinarith
lemma spill {t:Tower D}(i:Axis)(h:t=Region.next i r)(p:¬endsAt r i): K.sail t=K.sail r+P.val • step i:=by
 subst t; funext j; by_cases h:j=i <;> simp only [Planck.sail,Pi.add_apply,Pi.smul_apply,step_apply]; swap; · rw [next_at r i h, if_neg h, smul_zero, add_zero];
 subst j; unfold endsAt at p; rw [if_pos rfl,next_val r i,if_neg p,nsmul_eq_mul]; push_cast; ring
-- plane height gauge sites
abbrev upstairs' (n:Side) {g:Axis→Side} (r:Rail g)(i:Axis) : ℤ:= (n.val:ℤ)*((r i).val+1)
lemma next_motion {n:Side}(K:Planck (More n) P D){i:Axis}(p:¬endsAt r i)(z:Cover) : (plane i (upstairs' P r i)).motion (K.sail r+z)=K.sail (Region.next i r)+flipC P {i} z:=by
 rw [spill K r i rfl p]; funext j; simp only [fling_move,flip_iff,Pi.add_apply,Pi.smul_apply,step_apply]; by_cases h:i=j; · subst j; simp [Planck.sail,upstairs',nsmul_eq_mul]; ring
 simp [h,Ne.symm h]
lemma marched {n:Side}(K:Planck (More n) P D)(i:Axis)(p:¬endsAt r i)(u:Seat n)(v:u∈wallZ K r e) : (plane i (upstairs' P r i)).anon n u∈wallZ K (Region.next i r) e:=by
 obtain ⟨z,t,rfl⟩:= (seam ..).1 v; refine (seam ..).2 ⟨flipC P {i} z,fun j=>by specialize t j; rw [flip_iff]; split <;> omega,by rw [Planck.zone,Shape.anno, next_motion r K p]; rfl⟩ -- arg order
end Solid
-- use LAGER
namespace Burn
open Solid
variable {K:Calibration}(J:Tiling K){C:Conveyor K}{m:Side}(k:ℕ){p:K.takes m} {n:ℕ}
abbrev orderV (K:Calibration)(J:Tiling K){m:Side}(k:ℕ)(p:K.takes m) : Planck (More (cell m K.B K.R.L k)) (Domain (mesh J.d' K.R.L k) K.B) (J.qcount m):=(J.native_ord m p k).sugar K.B
abbrev glass {r:Tower (J.qcount m)} (p:K.takes m) := wallZ (orderV K J k p) r K.ℓ -- modify explicit
lemma solid_swell (r:Tower (J.qcount m))(p:K.takes m) : padded (apt m K.B K.R.L k) (glass J k (r:=r) p) (K.R.L.val*gross K.D K.w K.R.J) ⊆ glass J (k+1) (r:=r) p:= by
 let G:= apt m K.B K.R.L k; apply Subset.trans _ (solid_pad (orderV K J (k+1) p) r (margin_step K.buffer K.R.coarse)); apply Corona.halo_mono le_rfl; intro x hx; obtain ⟨z,h,rfl⟩:= mem_image.mp hx; exact swell (e:=K.ℓ) (orderV K J k p) (orderV K J (k+1) p) G ((ratio (apt J.d' K.B K.R.L k)).exact_size) r h
lemma gauged (K:Calibration) : 0 < K.ℓ := (Nat.zero_le _).trans_lt K.buffer
lemma rim (K:Calibration) : 2*(nearZero K.D+K.w)<K.ℓ :=by
 have he:= K.buffer; have hx:= K.R.coarse; unfold Margin r₃ r₁ at he; unfold nearZero; nlinarith
lemma land_far (p:K.takes m)(r t:Tower (J.qcount m))(u:r≠t)(x y:Seat (cell m K.B K.R.L k))(a:x∈glass J k (r:=r) p)(b:y∈glass J k (r:=t) p): 2*(nearZero K.D+K.w)<separation x y:=far_off (orderV K J k p) r (rim K) a b u
abbrev gaugedTop (K:Calibration)(J:Tiling K)(k:ℕ) := Domain (mesh J.d' K.R.L k) K.B
lemma plane_set (r:Tower (J.qcount m))(i:Axis): planeAt (upstairs' (gaugedTop K J 0) r i) K.R.L k=upstairs' (gaugedTop K J k) r i:=by
 induction k with
 | zero=>simp [planeAt]
 | succ k ih=>rw [←step_plane,ih,upstairs',upstairs',show (gaugedTop K J (k+1)).val=(gaugedTop K J k).val*K.R.L.val from (ratio (apt J.d' K.B K.R.L k)).exact_size]; push_cast; ring
namespace Bedded
variable {h:K.Allowed m n} {k:ℕ} (P:Bedded C h) {r:Tower (J.qcount m)} {A:Mark (K.c m)} {b:Bool}
include P J
lemma onGlass (p:k≤n)(a:AtSupport b (glass J 0 (r:=r) h.1) A): AtSupport b (glass J k (r:=r) h.1) (postV C m n k A):=by
 induction k with
 | zero=>exact a
 | succ k ih=> rw [postV_step]; exact (P.surrounds p (ih (by omega))).mono (solid_swell J k r h.1)
-- empty product
omit J
lemma hot_one (b:k<n): liner C m n k 1=1:=by
 let G:= apt m K.B K.R.L k; let E:=steps K.V m K.B n k
 letI: Nonempty (Forest (ratio G)):= Tree.select (ratio G) K.R.odd_side
 let ℒ:= cell m K.B K.R.L; let M:= (C.warm m n (k+1)).J.M; let A:=C.loom m k; let l:= assembled G K.K.j ((C.wave' n k).val) M K.R.odd_side K.η K.J.d A (1:Mark (ℒ k))
 have hw(F:Fields (ℒ (k+1)))(V: Pane (ℒ k)): l F V=1:=by
    unfold l assembled gathered avgF before
    simp_rw [Pi.one_apply,sub_one,sum_const,card_univ,← Nat.cast_smul_eq_nsmul (R:=ℝ)] -- tune
    have he:(Fintype.card (Forest (ratio G)):ℝ)≠0:=by positivity
    simp [inv_smul_smul₀ he]
 funext F; let β:= (C.warm m n (k+1)).beta; change linkLaw E β (l F) F.1=1; unfold linkLaw; simp_rw [hw]; rw [integral_smul_const,(E.isKernel ((Shots.warm_grant P.pair).branch k b) β).total,one_smul]
include J
variable (b:K.Allowed m n)
-- ext & product of finite list on definitely separated supports. No order swaps here.
lemma backed (Q:Tower (J.qcount m)→Mark (cell m K.B K.R.L k))(B:List (Tower (J.qcount m))) (u:∀ i, AtSupport false (glass J k (r:=i) h.1) (Q i)): AtSupport false (B.toFinset.biUnion fun i=> glass J k (r:=i) h.1) ((B.map Q).prod):=by
 induction B with
 | nil=>simpa using AtSupport.oneM (∅: Support _)
 | cons i B ih=> simp only [List.map_cons,List.prod_cons,List.toFinset_cons,biUnion_insert]; exact ((u i).mono subset_union_left).mulM (ih.mono subset_union_right)
lemma liner_prod (p:k<n)(Q:Tower (J.qcount m)→ Mark (cell m K.B K.R.L k))(B:List (Tower (J.qcount m)))(d:B.Nodup)(u:∀ i, AtSupport false (glass J k (r:=i) h.1) (Q i)): liner C m n k ((B.map Q).prod)=(B.map (fun i=> liner C m n k (Q i))).prod:=by
 induction B with
 | nil => simpa using P.hot_one p
 | cons i B ih => simp only [List.map_cons,List.prod_cons]; rw [P.hot_times p (u i) (backed J P Q B u),ih d.tail]; intro x t y v; obtain ⟨z,v,w⟩:= mem_biUnion.mp v; exact land_far J k h.1 i z (fun f=> (List.nodup_cons.mp d).1 (f.symm ▸ List.mem_toFinset.mp v)) x y t w
lemma coat_prod (p:k≤n)(Q:Tower (J.qcount m)→ Mark (K.c m))(B:List (Tower (J.qcount m)))(d:B.Nodup)(u:∀ i, AtSupport false (glass J 0 (r:=i) h.1) (Q i)): postV C m n k ((B.map Q).prod)=(B.map (fun i=> postV C m n k (Q i))).prod:=by
 induction k with
 | zero=> rfl
 | succ k ih=> rw [postV_step,ih (by omega),P.liner_prod J p _ B d (fun i=> P.onGlass J (by omega) (u i))]; simp_rw [postV_step]
end Bedded
end Burn
end YM.CF.Buffered
#print axioms YM.CF.Buffered.Burn.Bedded.coat_prod
