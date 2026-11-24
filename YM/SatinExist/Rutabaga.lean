import YM.SatinExist.Rutila
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxHeartbeats 330000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.SlabMark.Rutabaga
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common CF.Pannier.Chancel
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis Again
open CF.Lamour.Bridge.Celeste
open Sonnet
open CF.Lamour.Bridge.Celeste.SpotP
#check Chord
#check hyphen
#check fling_there
#check margin_separate
variable {K:Calibration}{N:Side}{M:Tulip.Male}{c f v z:ℝ}{p k r d B:ℕ}
variable (j:Axis) (u:ℕ) (X:Cover)
local notation "aλ"=> SpotP.Sylvia k r d p M f v c z
-- orientation of halo itself. price uses p only not necessarily K.ℓ; use u:=K.ℓ. Other axes unit extents B
structure Almost (k r d p:ℕ)(M:Tulip.Male)(f v c z:ℝ)(u B:ℕ)(x y:ℤ)(S:List (Sonnet N)):Prop where
   regular : SpotP.Sylvia k r d p M f v c z S
   mark : ∀ i∈ Broad p S,∃ t:ℤ,x+u≤t ∧ t+u≤y ∧ (t:Per (More N))=i j
   seat : ∀ a:Axis,a≠j → ∀ i∈ Broad p S,Chord (X a) B (i a)
local notation "ν"=> Almost j X k r d p M f v c z
-- parameter order ask
#check @Almost
variable {L R:List (Sonnet N)}{x y b:ℤ}
lemma Almost.mirror (A:ν u B x y L)(H:HaloTw k N) (n:ℤ): ν u B (2*n-y) (2*n-x) (L.map (fun a=>a.twistL j n)):=by
 refine ⟨A.regular.away j n H,?_,?_⟩
 · rw [Broad_turn]; intro m t; obtain ⟨q,h,rfl⟩:=mem_image.mp t; obtain ⟨b,p,vW,r0⟩:= A.mark q h
   refine ⟨2*n-b,by omega,by omega,?_⟩
   have hp:=across_coord j n q; rw [← r0] at hp; apply (sub_eq_iff_eq_add).mp at hp; rw [hp]; push_cast; ring
 rw [Broad_turn]; intro a h m t; obtain ⟨q,tu,rfl⟩:=mem_image.mp t;
 have hp:= A.seat a h q tu
 rw [show Shape.anon _ N q a=q a from ?_]; exact hp
 nth_rw 1 2 [←Rush.nat_true q]; rw [Shape.anno, wrap_here, wrap_here,fling_move,if_neg h.symm]
lemma Almost.desk (A:ν u B x y L)(e:y≤x+(N.val:ℤ)): Broad p L ⊆ band N j x u:=by
 intro m t; obtain ⟨b,hb,v,r'⟩:=A.mark m t
 rw [band_spec];
 rw [← r',← Int.cast_sub]; have hp:0≤ b-x:=by omega
 have hl:(b-x).toNat < (More N).val:=by change _< N.val*2; have hh:0 < N.val:=N.property; omega
 rw [← Int.toNat_of_nonneg hp,Int.cast_natCast,ZMod.val_natCast_of_lt hl]; omega
lemma Almost.tilt (A:ν K.ℓ B x y L)(h:y ≤ x+(N.val:ℤ))(H:HaloTw k N): Broad p L ⊆ hyphen j y (band N j y K.ℓ):=by
 intro m t; let z:=(plane j y).anon N m
 have hp:= Almost.mirror j K.ℓ X A H y
 rw [show 2*y-y=y from (by ring)] at hp
 refine mem_image.mpr ⟨z,(Almost.desk j K.ℓ X hp (by omega)) ?_,?_⟩
 · rw [Broad_turn]; exact mem_image_of_mem _ t
 exact fling_there j y m
lemma Almost.build (A:ν K.ℓ B x y L)(D:ν K.ℓ B y b R)(H:HaloTw k N)(s:x≤y)(h:y≤ x+(N.val:ℤ))(e:y≤b)(g:b≤ y+(N.val:ℤ)): ν K.ℓ B x b (L++R):=by
 have hd:Disjoint (Broad p L) (Broad p R):=(west K j y (band N j y K.ℓ) Finset.Subset.rfl).mono (Almost.tilt j X (K:=K) A h H) (Almost.desk j K.ℓ X D g)
 refine ⟨A.regular.tack D.regular hd,?_,?_⟩
 · rw [Broad_append]; intro m p; rcases mem_union.mp p with u|v'
   · obtain ⟨b,q,z,r⟩:= A.mark m u; exact ⟨b,q,z.trans e,r⟩
   obtain ⟨b,q,z,r⟩:= D.mark m v'; exact ⟨b,le_trans (by omega) q,z,r⟩
 rw [Broad_append]; intro a p i hi; exact (mem_union.mp hi).elim (A.seat a p i) (D.seat a p i)
variable (T:Family K→Mark N)
variable (Lm: ∀ X Y:Family K,T (X*Y)= T X * T Y)(Lt:T 1=1)(Lf:∀ (s:ℤ)(X:Family K), T (mirror K j s X)=reflMark j s (T X))
def Start (k r d p:ℕ)(M:Tulip.Male)(f v c z:ℝ)(B:ℕ)(x y:ℤ)(m:ℕ)(Y:Family K) : Prop := ∃ l:List (Sonnet N),Almost j X k r d p M f v c z K.ℓ B x y l ∧ l.length=m ∧ T Y=buffet l
local notation "α"=> Start j X T k r d p M f v c z B
variable (H : HaloTw k N)
variable {m n:ℕ}{F Z:Family K}
include H
include Lm
lemma Start.pack (A:α x y m F)(D:α y b n Z)(h:x ≤ y)(u:y ≤b)(v:y≤ x+(N.val:ℤ))(w:b≤ y+(N.val:ℤ)) : α x b (m+n) (F*Z) := by
 obtain ⟨l,t,r,s⟩:= A; obtain ⟨r',t',h',q⟩:= D
 refine ⟨_,Almost.build j X (K:=K) t t' H h v u w,by rw [List.length_append,r,h'],?_⟩
 rw [Lm,s,q,buffet_tack]
include Lf
omit Lm
lemma Start.recur (M:α x y m F)(t:ℤ) : α (2*t-y) (2*t-x) m (mirror K j t F):=by
 obtain ⟨l,a,r,s⟩:=M; exact ⟨_,Almost.mirror j K.ℓ X a H t,by rw [List.length_map,r],by rw [Lf,s,buffet_turn]⟩
lemma Start.addRoom(M:α x y m F)(b:ℤ): α (ruler K.B*b+x) (ruler K.B*b+y) m (relocate K j b F):=by
 let V:= Start.recur j X T Lf H M 0
 let W:= Start.recur j X T Lf H V (gaugeT K b)
 have d:2*(gaugeT K b)=ruler K.B*b:=ruler_offset ..; simp only [Int.mul_zero, Int.zero_sub, d, sub_neg_eq_add] at W
 exact W
variable (w:ℤ)(h:0<w)
include h
local notation "t!"=> ruler K.B*w
lemma Start.yacht (A:α 0 (t!) 1 F): α 0 (t!) 1 (toward K j w F n):=by
 induction n with
 | zero=> exact A
 | succ n ih=>
    have W:= Start.recur j X T Lf H ih (gaugeT K w);
    rw [ruler_offset,sub_self,sub_zero] at W; exact W
include Lm Lt
lemma ark (M':α 0 (t!) 1 F)(vt:t! * n ≤ (N.val:ℤ)): α 0 (t!*n) n (lace K j w F 1 n):=by
 have he:0<t!:=mul_pos (ruler_gene _) h
 induction n with
 | zero=> refine ⟨[],⟨⟨fun _ f=>(List.not_mem_nil f).elim,.nil⟩,?_,?_⟩,rfl,?_⟩
          · simp
          · simp
          exact Lt
 | succ n ih=>
    rw [Nat.cast_add_one] at vt
    have hv:= ih (by nlinarith)
    have W:= Start.addRoom j X T Lf H hv w; rw [add_zero] at W
    let B:=Start.pack j X T Lm H (Start.yacht j X T Lf H w h M' (n:=n)) W he.le (le_add_of_nonneg_right (by positivity)) (by nlinarith) (by linarith)
    convert B using 1 <;> (first | rfl | (push_cast; ring) | omega)
lemma largeL (A:α 0 (t!) 1 F)(e:2*(t!*n) ≤ (N.val:ℤ))(b:ℤ):
    ∃ (l:List (Sonnet N)), aλ l ∧ l.length=4*n ∧ T (banner j w b n F)=buffet l ∧ ∀ a:Axis,a≠j→ cows a (Broad p l) B:= by
 let d':= t!*n; let t:= ruler K.B*b
 have he: 0<t!:= mul_pos (ruler_gene _) h; have hv:0≤d':=by unfold d'; positivity
 have hp:=ark j X T Lm Lt Lf H w h A (n:=n) (by nlinarith)
 have hs:= Start.recur j X T Lf H hp 0; rw [mul_zero,zero_sub,sub_zero] at hs
 have hz:2*d' ≤ N.val:=e
 have G₀:=Start.pack j X T Lm H hs hp (by linarith) hv (by linarith) (by linarith);
 have W:= Start.addRoom j X T Lf H G₀ b
 let ζ:=t-d'
 change α (t+ -d') (t+d') (n+n) (chambers j w b F 1 n) at W
 rw [←sub_eq_add_neg] at W
 have U':= Start.recur j X T Lf H W ζ
 have d0:2*ζ - (t-d')=t-d':=by unfold ζ; ring
 have p₁:2*ζ-(t+d')≤t-d':=by unfold ζ; linarith
 have p₂:t-d'≤2*ζ-(t+d')+N.val:=by unfold ζ; linarith
 rw [d0] at U'
 obtain ⟨l,K₁,ht,hm⟩:= Start.pack j X T Lm H U' W p₁ (by linarith) p₂ (by linarith)
 have y: ζ= gaugeT K (cliff w b n):=by rw [centered_index]; unfold ζ t d'; ring
 exact ⟨l,K₁.regular,by omega,by rw [y] at hm; exact hm,fun i v=>⟨X i,K₁.seat i v⟩⟩
end YM.CF.Buffered.Afterglow.Tower.SlabMark.Rutabaga
