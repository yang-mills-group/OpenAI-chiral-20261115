import SatinThinRenew
import YM.SU5.FiniteGaugeData.Tower.Central
set_option synthInstance.maxSize 28000
set_option maxRecDepth 6000
set_option maxHeartbeats 240000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.SlabMark.ArrayParcel
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Heat Analysis
set_option autoImplicit false
open Again CF.Pannier.Chancel

/-! # Banners: long arrays of polarized marks simultaneously at two resolutions
Mirrors of the actually represented insertions computed at high
resolution; time parcel (for packing) checked at low. -/

variable {K:Calibration}{N M:Side}
structure Conveys (q:ℤ)(Z:Family K→Mark M)(p:Site N→Mark M):Prop where
 empty: Z 1=1
 add: ∀ F G,Z (F*G)=Z F*Z G
 reflect: ∀ (F:Family K)(l:List (Site N)),Z F = (l.map p).prod →
    ∀ i s,Z (Tower.mirror K i (q*s) F)= ((spun i s l).map p).prod

abbrev Room (i:Axis)(D:ℕ)(a b:ℤ)(x: Seat N):=
  ∃ s:ℤ, a+D<s∧s+D<b∧ (s:Per (More N))=x i
variable {i:Axis}{a b x:ℤ}{D:ℕ}
lemma costs_space {S T:Seat N}(p:Room i D a b S)(w:Room i D b x T)
    (h:x-a ≤ (More N).val):
    D < separation S T:=by
  obtain ⟨z,l,r,hz⟩:=p; obtain ⟨y,l',r',hy⟩:=w
  by_contra! he
  let u:ℤ:= Lattice.lift (S-T) i
  have ha:u.natAbs≤D:=(component_le (S-T) i).trans he
  have t:((More N).val:ℤ) ∣ (u-(z-y):ℤ):=
    (ZMod.intCast_eq_intCast_iff_dvd_sub ..).mp (show (u:Per (More N))=((z-y:ℤ):Per (More N)) by rw [Int.cast_sub,hz,hy];exact congr_fun (wrap_lift (S-T)) i).symm
  have s:= Int.le_of_dvd (show 0 < u-(z-y) by omega) t
  omega

lemma spun_room {S:Seat N}(p:Room i D a b S)(v:ℤ) :
    Room i D (2*v-b) (2*v-a) ((plane i v).anon N S):=by
  obtain ⟨z,l,r,h⟩:=p
  refine ⟨2*v-z,by omega,by omega,?_⟩
  simp [plane,Shape.anon,affine,Signed.mirror,Signed.act,wrap_here,h]
  ring
private lemma anon_cross (i j:Axis)(e:j ≠ i)(s:ℤ)(x:Seat N) : (plane i s).anon N x j=x j := by
  simp [plane,Shape.anon,affine,Signed.mirror,Signed.act,wrap_here,e,e.symm]
variable (i:Axis){X:Axis→ℤ}{F: Family K}
/-- Invoice. Length and location measured in N (low) pixels. -/
def Parcel (Z:Family K→Mark M)(p:Site N→Mark M)
    (i:Axis) (D B:ℕ)(X:Axis→ℤ)(a x:ℤ)(l:ℕ)(F:Family K):Prop:=
  ∃ t:List (Site N), outdoor D t ∧ Z F=(t.map p).prod ∧ t.length=l ∧ 
      (∀ y∈t,Room i D a x (node y)) ∧
      ∀ j:Axis,j≠i → ∀ y∈t, Chord (X j) B (node y j)
variable {p:Site N→Mark M}{Z:Family K→Mark M}{l B:ℕ}
variable {q:ℤ}(h:Conveys q Z p)
local notation "ℭ" a:max x:max m:max F:max => Parcel Z p i D B X a x m F
local notation "c₀"=> ruler K.B
include h

private lemma reflects (f:ℭ a x l F)(n:ℤ):
    ℭ (2*n-x) (2*n-a) l (Tower.mirror K i (q*n) F):=by
 obtain ⟨t,f,g,k,W,u⟩:=f
 refine ⟨spun i n t,List.pairwise_map.mpr ?_,h.reflect F t g i n,by rwa [Again.spun,List.length_map],?_,?_⟩
 · refine f.imp (by intro x y f; simp only [Shape.nodex,Shape.anon,affine,separation_translate,separation_signed]; exact f)
 · intro _ z; obtain ⟨x,e,rfl⟩:= List.mem_map.mp z; rw [Shape.nodex]; exact spun_room (W _ e) n
 intro j v _ z; obtain ⟨x,e,rfl⟩:=List.mem_map.mp z
 rw [Shape.nodex,anon_cross i j v]
 exact u j v x e

private lemma androgyny {Y:Family K}{r:ℕ}
   (f:ℭ a b l F)(g:ℭ b x r Y)
   (v:x-a ≤ ((More N).val:ℤ))(e:a≤b)(u:b≤x): ℭ a x (l+r) (F*Y):=by
 obtain ⟨t,w,g',k,V,z⟩:=f; obtain ⟨s,w',g,ℓ,U,z'⟩:=g
 refine ⟨t++s,List.pairwise_append.mpr ⟨w,w',fun _ p _ q=>costs_space (V _ p) (U _ q) v⟩,?_,by rw [List.length_append,k,ℓ],?_,?_⟩
 · rw [h.add,g',g,List.map_append,List.prod_append]
 · intro y h'
   rcases List.mem_append.mp h' with t|t
   · obtain ⟨j,w,r,o⟩:= V _ t; exact ⟨j,w,r.trans_le u,o⟩
   obtain ⟨j,w,r,o⟩:= U _ t; exact ⟨j,lt_of_le_of_lt (add_le_add_left e _) w,r,o⟩
 intro j p y t; exact (List.mem_append.mp t).elim (z _ p _) (z' _ p _)
private lemma scale_t (n:ℤ):q*gaugeT K n = gaugeT K (q*n):=by unfold gaugeT Heat.gaugeShift; ring
private lemma displaced (p:ℭ a x l F)(v:ℤ) :
    ℭ (c₀*v+a) (c₀*v+x) l (relocate K i (q*v) F):= by
 have e:=reflects i h (reflects i h p 0) (gaugeT K v)
 rw [scale_t (h:=h),ruler_offset] at e
 ring_nf at e ⊢; exact e

private lemma vintage {u : ℤ} (p:ℭ 0 (c₀*u) l F)(r:ℕ) : ℭ 0 (c₀*u) l (toward K i (q*u) F r):=by
 induction r with
 | zero=> exact p
 | succ r ih=>
    rw [toward_step]; have e:=reflects i h ih (gaugeT K u)
    rwa [scale_t (h:=h),ruler_offset, sub_self,sub_zero] at e

private lemma lacework {u : ℤ} (p:ℭ 0 (c₀*u) 1 F)(y:0≤u)(r:ℕ)
   (v:c₀*u*r ≤ ((More (N)).val:ℤ)) : ℭ 0 (c₀*u*r) r (lace K i (q*u) F 1 r) := by
 induction r with
 | zero=> exact ⟨[],List.Pairwise.nil,h.empty,rfl,by simp,by simp⟩
 | succ r ih=>
    have ht :0≤ c₀*u:=mul_nonneg (ruler_gene K.B).le y
    rw [Nat.cast_add_one] at v ⊢
    let L:=toward K i (q*u) F r; let C:=lace K i (q*u) F 1 r
    have hh:=ih (le_trans (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le_one) ht) v)
    rw [lacing]
    have hd:=displaced i h hh u; rw [add_zero] at hd
    have hep:=androgyny i h (vintage i h p r) hd (by nlinarith) ht (by nlinarith)
    rw [mul_add,mul_one,add_comm (c₀*u*↑r),Nat.add_comm]; exact hep

lemma banners {u : ℤ}(p:ℭ 0 (c₀*u) 1 F)(y:0≤u)(r:ℕ)
   (v:2*(c₀*u*r)≤ ((N).val:ℤ))(s:ℤ):
   let H:=c₀*(s-u*r); ℭ (H-2*(c₀*u*r)) (H+2*(c₀*u*r)) (4*r) (SlabMark.banner i (q*u) (q*s) r F):= by
 intro H'
 let C:= c₀*u*r; let L:= lace K i (q*u) F 1 r; let S:= chambers i (q*u) (q*s) F 1 r
 have hp:0≤ c₀*u*r:= mul_nonneg (mul_nonneg (ruler_gene K.B).le y) (by positivity)
 have hh: ((More N).val:ℤ)=2*(N.val:ℤ):=by change ((↑(N.val*2):ℤ)=_); push_cast; ring
 have he:= lacework i h p y r (by linarith)
 have ht:=reflects i h he 0; rw [mul_zero, zero_sub,sub_zero, mul_zero] at ht
 have hd:= androgyny i h ht he (by linarith) (by linarith) hp; have hk:=displaced i h hd s
 have hΩ : ℭ H' (H'+2*C) (r+r) S:= by
    rw [show H'+2*C = c₀*s+c₀*u*↑r by unfold C H'; ring,show H'=c₀*s+ -(c₀*u*r) by unfold H'; ring]; exact hk
 have hL:=reflects i h hΩ (gaugeT K (cliff u s r))
 have hy : gaugeT K (cliff u s r)=H':= centered_index (K:=K) u s r
 rw [show 2*gaugeT K (cliff u s r)-(H'+2*C)=H'-2*C by rw [hy]; ring, show 2*gaugeT K (cliff u s r)-H'=H' by rw [hy]; ring] at hL
 rw [scale_t (h:=h) (cliff u s r), show q * cliff u s r = cliff (q*u) (q*s) r by unfold cliff; ring] at hL
 rw [show 4*r=r+r+(r+r) by omega]; exact androgyny i h hL hΩ (by linarith) (by linarith) (by linarith)

lemma tally {u:ℤ}(y:0≤u)(r:ℕ)
    (v:2*(ruler K.B*u*r) ≤ ((N).val:ℤ))(s:ℤ)
    (D B:ℕ)
    (t:Site N)(w:Z F = p t)
    (b: Room i D 0 (ruler K.B*u) (node t)):
    ∃ l:List (Site N), outdoor D l ∧ l.length=4*r ∧
      Z (SlabMark.banner i (q*u) (q*s) r F)=(l.map p).prod ∧
      ∀ j,j≠i→cows j (upperRoll l) B:=by
 let X := Lattice.lift (node t)
 have k: Parcel Z p i D B X 0 (ruler K.B*u) 1 F:=by
   refine ⟨[t],List.pairwise_singleton _ _,by simpa using w,rfl,by simpa using b,?_⟩
   simpa only [List.mem_singleton,forall_eq] using (show ∀ j:Axis,j≠i→Chord (X j) B (node t j) from fun j _=> ⟨X j,le_rfl,by omega,congr_fun (wrap_lift (node t)) j⟩)
 obtain ⟨l,o,a',e,_,z⟩:=banners i h k y r v s
 refine ⟨l,o,e,a',fun j b=>⟨X j,?_⟩⟩
 intro w p'; obtain ⟨x,p,rfl⟩:=List.mem_map.mp (List.mem_toFinset.mp p')
 exact z _ b _ p

end YM.CF.Buffered.Afterglow.Tower.SlabMark.ArrayParcel
