import Merino.Garter.Silver
import YM.SU5.Thin.Glacier.Hilltop
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 600000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Merino.Garter
open Function Lattice Finset RG Wilson Metric Exterior Work.F03
open Regis.Head MeasureTheory
open scoped Topology ContDiff InnerProductSpace Classical Matrix.Norms.Frobenius
variable {n:Side}{G:Gauge}

open Cuff Hem
variable {I:Type*}
open Tree Filter Precision Next.Rank.Spindle Pressure ProbabilityTheory
open Gleam Next.SectorChange Next.SectorChange.Gaussian
open Etch -- (includes river)
open StepIn
variable {c:Side}{r:Ratio c n}{H:Bed}{m:ℕ}{p:BudgetPoint}{q:Clip}{v η S C δ w β:ℝ}{A:Support c}{N:Finset (Cell n)}{Z:PathData G}

def wiggle (m:ℕ):ℕ:=m/100
def living (m:ℕ):ℕ:=hallBill m - wiggle m
abbrev shellC (m:ℕ):=m+16

variable {X Y:Dir G n}{U:Config G n}{a:StepIn n}{R:Rules G}

lemma mild {j:ℕ}{o:Site n}{b:Cell n}(d:Deep r A N j o)
   (h:N=meek p U)(y:separation o b.1 ≤ j) :
   G.chord (faceValue U b)<p.threshold:=by
 apply lt_of_le_of_lt _ (half_lt_self p.threshold_pos)
 by_contra! e
 have v:b∈N:=h.symm ▸ (mem_filter.mpr ⟨mem_univ _,e⟩:b∈meek p U)
 exact (d.2 b v).not_ge y

lemma patron(h:400≤ m)(d:Deep r A N (living m) a.there)
   (g:N=meek p U): Lave p.threshold (Yardlet n (shellC m)) (a.cabin U):=by
 intro b hb; rw [a.posted]; apply mild d g
 obtain ⟨y,v,z⟩:=Finset.not_disjoint_iff.mp hb
 have l:separation 0 y≤ m+16:=by simpa [Yardlet,halo_spec] using v
 refine (a.toll b).trans ?_
 have t:=separation_triangle 0 y b.1
 have u:=Work.E01.sep_touched b y z
 rw [separation_comm b.1] at u
 unfold living hallBill Sequest wiggle
 omega


abbrev flex(a:StepIn n)(V:Dir G n):= collect G (a.steer V)
lemma usher(h:400≤ m)(d:Deep r A N (living m) a.there)(q₀:TrustLogs Y U r A v)
    (t:v≤R.c) :
   Agrees (Yardlet n (shellC m)) (a.cabin U) (increment 1 (flex a Y)):=by
 have he:=bank_at a.face a.there Y 1
 rw [one_smul,one_smul] at he
 change Agrees _ _ (represent _)
 rw [he]; apply a.agrees
 intro b hb _
 have l:separation a.there b.1 ≤ m+16:=by simpa [baseball,halo_spec] using hb
 have hd:=d.1.shift (y:=b.1) (e:=1) (by unfold living hallBill wiggle Sequest; omega)
 obtain ⟨u,w⟩:=q₀ b ⟨hd.1,safeIn hd le_rfl⟩
 rw [represent_link,show Y (b.1,coord b.2)=_ from u, R.records _ (w.trans t)]
lemma flex_slim (p':ProbeBox Y v)(t:0≤v): ‖flex a Y‖ ≤ v:=by
 refine (pi_norm_le_iff_of_nonneg t).mpr fun i=>?_
 have h:=congrArg Multiplicative.toAdd (congr_fun (read_bank a.face a.there Y) i)
 change flex a Y i=_ at h
 rw [h]
 unfold pull Step.read
 split
 · rw [toAdd_inv,norm_neg]; exact p' _
 exact p' _


lemma Gem_cost(i:Chips G)(e:G.Color):|dust i e|≤‖e‖:=by 
 simpa only [EuclideanSpace.basisFun_inner,OrthonormalBasis.norm_eq_one,one_mul] using (abs_real_inner_le_norm (EuclideanSpace.basisFun (Chips G) ℝ i) e)
variable (B:Z.Bounds q η C S)(P:Attached H Z)
lemma flowAt {b:Cell n}(g:rimB r A m N b):
 river q b (iceCost B P r A m N Y β X) = Real.sqrt β • faceCurl b (X+Y):=by
 rw [iceCost,map_smul,coupling,inv_inv,← river_now q B P]
 rw [map_add (tiler B P)]; congr 1; ext i
 unfold river cup; simp [accessN,g]


variable {f:Config G n→ℂ}{T:Bundle G n}
local notation "Cr"=>iceCost
lemma mintCore(h:400≤ m)(d:Deep r A N (living m) a.there)
    (g:N=meek p U)
    (l:TrustLogs (X+Y) U r A v)(k:0≤v)(j:v≤R.c)
    (i:Husk G n)(e:separation 0 i.1.1 ≤ slim (shellC m)):
    let y:=silver q a i (iceCost B P r A m N Y β X)
    y=Real.sqrt β * cseed (flex a (X+Y)) i ∧
    |y| ≤ Real.sqrt β * (p.threshold+faceCutError R v):=by
 intro y
 let b:=a.sent i.1
 have H:rimB r A m N b:=by
   refine d.turn ((Nat.add_le_add_right
     (k:=Sequest m) (a.toll i.1)) |>.trans ?_)
   unfold slim shellC at e
   unfold living hallBill wiggle Sequest
   omega
 have yu:y=a.cost i.1 * dust i.2 (Real.sqrt β • faceCurl b (X+Y)):=by
   unfold y; rw [silver_at,flowAt B P H]


 rw [yu]
 constructor
 · unfold cseed cref flex; rw [fundamental]; 
   change _=Real.sqrt β * dust i.2 (faceCurl i.1 _)
   rw [a.swirl]
   simp [dust,b,mul_left_comm]
 have hs:Gleam.Safe r A 4 b.1:=H.1.shift (by simp [Sequest])
 have u:‖faceCurl b (X+Y)‖ ≤ _:= (norm_le_norm_add_norm_sub (G.curvature (faceValue U b)) _).trans
   (add_le_add ((G.curvature_norm _).trans (mild H g (by simp)).le)
      (angleFaceSmall l k j b hs).2)
 rw [abs_mul, show |a.cost i.1| =1 from orient_abs ..,one_mul]
 refine (Gem_cost ..).trans ?_
 rw [norm_smul,Real.norm_of_nonneg (Real.sqrt_nonneg _)]
 exact mul_le_mul_of_nonneg_left u (Real.sqrt_nonneg _)


lemma payment {τ L E:ℝ}
 (t:Scar (shellC m) p.threshold τ L E f T)(ht:2*v ≤ τ)
 (h:400 ≤ m)(d:Deep r A N (living m) a.there)(y:0 ≤ β)
    (g:N=meek p U)
    (l:TrustLogs (X+Y) U r A v)(k:0≤v)(j:v≤R.c)
    (x:ProbeBox (X+Y) (2*v)) :
   let e:=iceCost B P r A m N Y β X
   ‖(β:ℂ)*f (a.cabin U)-gloss T q a e‖≤β*(L*(2*v)^3+E)
    ∧ ∀ i:Husk G n, separation 0 i.1.1 ≤ slim (shellC m) →
     |silver q a i e| ≤ Real.sqrt β * (p.threshold+faceCutError R v):=by
 intro e; constructor
 swap; · exact fun i u=>(mintCore B P (β:=β) h d g l k j i u).2
 let V:=flex a (X+Y)
 let u:=cseed V
 let p₀:=dripQ T u u
 have hz:0≤L:=(norm_nonneg _).trans (t.bound U)
 have hu:gloss T q a e=β*p₀:=by
   have z:=dripQ_quad T (Real.sqrt β) u
   rw [Real.sq_sqrt y] at z
   apply Eq.trans _ z
   unfold gloss dripQ; dsimp only
   exact sum_congr rfl fun q _=>sum_congr rfl fun r _=>by 
     by_cases i:T q r=0
     · simp [i]
     obtain ⟨c,g'⟩:=t.cloth.both i
     rw [(mintCore B P (β:=β) h d g l k j _ c).1,
         (mintCore
            B P (β:=β) h d g l k j _ g').1]
     rfl
 rw [hu,Complex.ofReal_mul,← mul_sub,norm_mul,Complex.norm_real,Real.norm_of_nonneg y]
 apply mul_le_mul_of_nonneg_left _ y
 have he: ‖V‖≤2*v:= flex_slim x (by positivity)
 refine (t.debt _ _ (he.trans ht) (patron h d g) (usher h d l j)).trans
   (add_le_add_left ?_ _)
   <;> exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) he _) hz

end YM.CF.Merino.Garter
