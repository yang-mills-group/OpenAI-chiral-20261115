import YM.SU5.FiniteGaugeData.Tower.PureCap
import ZecaCrew
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 6000
set_option maxHeartbeats 420000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.SlabMark.Cardigan
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis
set_option linter.unusedSectionVars false
set_option linter.style.whitespace false
set_option maxHeartbeats 800000

/-! Make exact sparse lists at terminal banner length using projection
width on N (R times for actual stamps). All RP done later. -/
open CF.Pannier.Chancel

variable {α:Type*}{N:Side}
/-- Interior interval in Seat units modulo twice side. -/
def InBend (j:Axis)(a b:ℤ)(D:ℕ)(z:Seat N):Prop:=
 ∃ y:ℤ,(↑y:Per (More N))=z j ∧ a+D≤y ∧ y+D≤b
lemma InBend.reverse {j:Axis}{z:Seat N}{a b:ℤ}{D:ℕ}
 (h:InBend j a b D z)(s:ℤ):
 InBend j (2*s-b) (2*s-a) D ((plane j s).anon N z):=by
 obtain ⟨y,v,t,w⟩:=h
 refine ⟨2*s-y,?_,by omega,by omega⟩
 rw [Int.cast_sub,Int.cast_mul,Int.cast_ofNat,v,
     eq_add_of_sub_eq (across_coord j s z)]; ring
lemma InBend.band' {j:Axis}{z:Seat N}{a b s:ℤ}{D:ℕ}
 (h:InBend j a b D z)(p:s≤a)(q:b ≤ s+N.val):
 z∈band N j s D:=by
 obtain ⟨y,e,u,v⟩:=h
 have t : (y-s).toNat < (More N).val:= by change _<N.val*2; have hp:0<N.val:= N.property; omega

 have r : z j - (s:Per (More N))= (↑(y-s).toNat:Per (More N)):= by
    rw [←Int.cast_natCast,Int.toNat_of_nonneg (by omega),Int.cast_sub,e]
 rw [band_spec,r,ZMod.val_natCast_of_lt t]
 omega
lemma InBend.mono {j:Axis}{z:Seat N}{a b s t:ℤ}{D:ℕ}
 (h:InBend j a b D z)(p:s≤a)(q:b≤t):InBend j s t D z:=by
 obtain ⟨y,r,u,v⟩:=h
 exact ⟨y,r,by omega,by omega⟩
private lemma sameCross (i j:Axis)(e:i≠j)(s:ℤ)(x:Seat N):
 (plane j s).anon N x i=x i:=by
 simp [plane,Shape.anon,affine,Signed.mirror,Signed.act,wrap_here,e,e.symm]

variable {K:Calibration}{m M:Side}(γ:K.c m=M){w T D:ℕ}
  {R:ℤ}{ρ:α→Seat N}{χ:Axis→ℤ→α→α}{p:α→Mark M}
  {V:Mark M→ℂ}(h:Grace K.B ρ χ D T p V (fun i=>R*i) w)

-- Proof object independent of χ
def Ribbon (γ:K.c m=M)(j:Axis)
 (p:α→Mark M)(ρ:α→Seat N)(D T:ℕ)(z:Seat N)
 (a b:ℤ)(F:Family K)(n:ℕ):Prop:=
 TestFamily K true F ∧
 ∃ l:List α,l.length=n ∧ outdoor ρ T l ∧
    (∀ x∈l, InBend j a b D (ρ x)) ∧

    (∀ x∈l, ∀ i:Axis,i≠j→ρ x i=z i) ∧ ship γ (F m)=(l.map p).prod
variable {γ}{j:Axis}{z:Seat N}
local notation "Y"=>Ribbon γ j p ρ D T z
local notation "U"=>ruler K.B
lemma Ribbon.nil (a b:ℤ): Y a b 1 0:=by
 refine ⟨aux_test (S:=∅) InTest.one, [],rfl,List.Pairwise.nil,by simp,by simp,?_⟩
 exact (ship_arith γ 0 0 0).2.2.2.1
lemma Ribbon.single {a b:ℤ}{F:Family K}{seed:α}
 (u: TestFamily K true F)(v:ship γ (F m) = p seed)
 (y:InBend j a b D (ρ seed)):
 Ribbon γ j p ρ D T (ρ seed) a b F 1:=by
 refine ⟨u,[seed],rfl,?_,by simpa using y,by simp,by simpa using v⟩
 exact List.pairwise_singleton ..
include h
lemma Ribbon.rev {a b:ℤ}{F:Family K}{n:ℕ}
 (hx:Y a b F n)(y:ℤ):
 Y (2*y-b) (2*y-a) (mirror K j (R*y) F) n:= by
 obtain ⟨f,l,m',g,r,c,v⟩:=hx
 refine ⟨reflect_ok K j _ f,spun χ j y l,by simp [spun,m'],List.pairwise_map.mpr ?_,?_,?_,?_⟩
 · refine g.imp (by intro x u a; simp only [h.nodex,Shape.anon,affine,separation_translate,separation_signed]; exact a)

 · intro x u; obtain ⟨x,t,rfl⟩:=List.mem_map.mp u
   rw [h.nodex]; exact (r x t).reverse _
 · intro x u i t; obtain ⟨x,g,rfl⟩:=List.mem_map.mp u
   rw [h.nodex,sameCross i j t]; exact c x g i t
 unfold mirror
 rw [(ship_arith γ (F m) 0 0).2.2.2.2,v,spun_price h]
 -- maybe rfl
lemma Ribbon.send_for {a b:ℤ}{F:Family K}{n:ℕ}
 (hx:Y a b F n)(y:ℤ):
 Y (U*y+a) (U*y+b) (relocate K j (R*y) F) n:= by
 have he: R*gaugeT K y - R*0=gaugeT K (R*y):=by unfold gaugeT gaugeShift; ring
 have hy:= (hx.rev h 0).rev h (gaugeT K y)
 rw [ruler_offset, mirror_at K j he hx.1] at hy
 simpa only [mul_zero,zero_sub, sub_neg_eq_add] using hy
/-- Adjoining two projected lists with meeting plane s.
Each width ≤ N (total may be larger). -/
lemma Ribbon.grow {a b s:ℤ}{F G:Family K}{l n:ℕ}
 (hx:Y a s F n)(hy:Y s b G l)
 (t:a ≤ s)(u:s≤b)(v:s≤a+N.val)(y:b ≤ s+N.val):
 Y a b (F*G) (n+l):=by
 obtain ⟨f,z1,m1,g1,r1,c1,v1⟩:=hx
 obtain ⟨g,z2,m2,g2,r2,c2,v2⟩:=hy
 refine ⟨f.mul g,z1++z2,by simp [m1,m2],
    List.pairwise_append.mpr ⟨g1,g2,?_⟩,?_,?_,?_⟩

 · intro i e k t'
   have hi:ρ i ∈ (band N j s D).image ((plane j s).anon N):=by
     refine mem_image.mpr ⟨(plane j s).anon N (ρ i),((r1 i e).reverse s).band'
        (by omega) (by omega),?_⟩
     funext a
     by_cases ha:a=j
     · rw [ha, eq_add_of_sub_eq (across_coord j s _),eq_add_of_sub_eq (across_coord j s (ρ i))]
       abel
     rw [sameCross a j ha,sameCross a j ha]
   have hk:ρ k ∈ band N j s D:=(r2 k t').band' (le_refl _) y
   rw [separation_comm]; have ht:=h.gap
   exact ht.trans_le (opposite_gap _ _ (by omega:D>0) _ _ hk hi)
 · intro i e; rcases List.mem_append.mp e with e|e
   · exact (r1 i e).mono le_rfl u
   exact (r2 i e).mono t le_rfl
 · intro i e; rcases List.mem_append.mp e with e|e
   · exact c1 i e
   exact c2 i e
 change ship γ (F m * G m) = _
 rw [(ship_arith γ (F m) _ 0).2.1,v1,v2,List.map_append,List.prod_append]

variable (w₀:ℤ)(F:Family K)
    (hx:Ribbon γ j p ρ D T z 0 (ruler K.B*w₀) F 1)
local notation "W"=>R*w₀
local notation "μ"=>U*w₀ -- macro prec danger
include hx
lemma Ribbon.front (n:ℕ): Y 0 (U*w₀) (toward K j (R*w₀) F n) 1:= by
 induction n with
 | zero=>exact hx
 | succ n ih=>
    have t := ih.rev h (gaugeT K w₀)
    have hg: R*gaugeT K w₀=gaugeT K (R*w₀):=by unfold gaugeT gaugeShift; ring
    rw [ruler_offset,sub_self,sub_zero,hg] at t; exact t
lemma Ribbon.dawn (a:0<w₀) (n:ℕ)(u:μ*n ≤ (N.val:ℤ)):
 Y 0 (μ*n) (lace K j (R*w₀) F 1 n) n:= by
 have e:=ruler_gene K.B
 have hr:0<μ:=mul_pos e a
 induction n with
 | zero=> exact Ribbon.nil _ _
 | succ n ih=>
    rw [Nat.cast_add_one] at u
    have x := ih (show μ*n ≤ (N.val:ℤ) by linarith only [u,hr])
    have t:=x.send_for h w₀
    rw [add_zero] at t
    have hd:=Ribbon.grow h (Ribbon.front h w₀ F hx n) t hr.le
      (le_add_of_nonneg_right (mul_nonneg hr.le (Int.natCast_nonneg _)))
      (by nlinarith) (by nlinarith)
    rw [add_comm 1 n] at hd
    rw [Nat.cast_add_one]
    rw [show μ*((n:ℤ)+1)=μ+μ*n by ring]
    exact hd -- goal order lacing? Nat.add_comm rewrites n+1 in lace!

lemma Ribbon.twain (a:0<w₀)(n:ℕ)(u:μ*n ≤ (N.val:ℤ))(i:ℤ):
 Y (μ*i-μ*n) (μ*i+μ*n)
    (chambers j (R*w₀) ((R*w₀)*i) F 1 n) (2*n):=by
 have hr:0≤μ*n:=by have h':=ruler_gene K.B; positivity
 have l:=Ribbon.dawn h w₀ F hx a n u
 have r:=l.rev h 0
 rw [mul_zero,zero_sub,sub_zero,mul_zero] at r
 have t:=(r.grow h l (by linarith) hr (by linarith) (by linarith)).send_for h (w₀*i)
 rw [←mul_assoc U,←mul_assoc R w₀,← two_mul n,← sub_eq_add_neg] at t
 exact t

lemma Ribbon.empire (a:0<w₀)(n:ℕ)
 (u:2*(μ*n)≤ (N.val:ℤ))(i:ℤ):
 ∃ a b,Y a b (banner j (R*w₀) ((R*w₀)*i) n F) (4*n):=by
 have hr:0≤μ*n:=by have h':=ruler_gene K.B; positivity
 have l:=Ribbon.twain h w₀ F hx a n (by linarith) i
 let x:ℤ:=μ*i-μ*n
 let y:ℤ:=μ*i+μ*n
 change Y x y _ _ at l
 have r := l.rev h x
 rw [show 2*x-x=x by ring] at r

 have hu:x≤y:=by unfold x y; linarith only [hr]
 have hv:y≤x+N.val:=by unfold x y; linarith only [u]
 have hs:= r.grow h l (by linarith) hu (by linarith) hv
 have hc : R*x=gaugeT K (cliff (R*w₀) ((R*w₀)*i) n):=by
    rw [centered_index]
    unfold x; ring
 rw [hc, show 2*n+2*n=4*n by omega] at hs
 exact ⟨_,_,hs⟩

/-- A mosaic, retaining the output length licenses, arbitrary admissible n.
`y.length` is extensive both from below at projection cost and from
above at current-site cost (if M dominates). -/
lemma full_bloom (a:0<w₀) (u:ℕ) (p0:μ=u)
 (ht:Again.plusAgain K.B D≤2*u)
 (n:ℕ)(b:2*(μ*n)≤(N.val:ℤ))
 (d:(N.val:ℤ)≤4*(μ*n))
 (i:ℤ) {C:ℝ}(he:pay F C):
 ∃ (y: List α)(g:ℕ),outdoor ρ T y ∧ y.length=g*(4*n) ∧
 (∀ x:Fields M,‖(y.map p).prod x‖ ≤ C^y.length) ∧
 ‖V (ship γ (banner j (R*w₀) ((R*w₀)*i) n F m))‖^g ≤ ‖V (y.map p).prod‖ ∧
 0<g ∧ y.length≤(More N).val^4 ∧
 (More N).val^4 ≤ y.length*(8*u)^4:=by
 let B₁:=banner j (R*w₀) ((R*w₀)*i) n F
 obtain ⟨_,_,_,l,lx,t,_,c,ll⟩:=Ribbon.empire h w₀ F hx a n b i
 have hn : 1≤n :=by
    by_contra! ha; rw [show n=0 by omega,Nat.cast_zero,mul_zero,mul_zero] at d
    have hw:0<N.val:=N.property; omega
 have ho : 1≤μ:=by have hw:=ruler_gene K.B; nlinarith

 have hq: Again.plusAgain K.B D ≤ N.val:=by
    refine ht.trans ?_
    apply Int.ofNat_le.mp
    push_cast
    nlinarith [show (1:ℤ)≤n by exact_mod_cast hn]
 have hM: l.length ≤ (More N).val:=by
    change _≤N.val*2; rw [lx]; apply Int.ofNat_le.mp; push_cast
    nlinarith [Int.natCast_nonneg n]
 have hv : N.val≤u*l.length:=by rw [lx]; apply Int.ofNat_le.mp; push_cast; nlinarith
 have hE : ∀ x:Fields M, ‖(l.map p).prod x‖ ≤ C^(4*n):=by
    rw [←ll]; exact reward γ _ _ (main_bill _ _ _ n hx.1 he).2
 have hz : ∀ i,i≠j→cows i (upperRoll ρ l) 0:=by
    intro i e; refine ⟨((z i).val:ℤ),?_⟩
    intro x lx; obtain ⟨x,g,rfl⟩:=List.mem_map.mp (List.mem_toFinset.mp lx)
    refine ⟨((z i).val:ℤ),by omega,by omega,?_⟩
    rw [Int.cast_natCast,c x g i e,ZMod.natCast_zmod_val]
 obtain ⟨y,g,k,yy,f,ig,t,m,d⟩:=transverse h l j hq ht hM hv t hz hE
 refine ⟨y,g,k,?_,?_,by rw [ll]; exact ig,t,m,d⟩
 · rw [yy,lx]
 rw [yy,lx,Nat.mul_comm g,pow_mul]; exact f
where
 reward {K:Calibration}{m d:Side}(w:K.c m=d)(x:Family K)(q:ℝ)(t:pay x q):
  ∀ j,‖ship w (x m) j‖≤q:=by subst d; exact t m
end YM.CF.Buffered.Afterglow.Tower.SlabMark.Cardigan
