import YM.CF.BProof.Mote.Motif
import YM.CF.Broc.Mint
import YM.CF.Dial.Pry
set_option autoImplicit false
noncomputable section
namespace YM.CF.Peaks
open Function Filter Lattice Laurent Bloch Next.Free Metric Lat Finset Branch Cube Tenant SU Rush Drapes Fir Tulip
open scoped Topology Matrix BigOperators Matrix.Norms.L2Operator Kronecker Classical
attribute [local instance] opCStarAlgebra
variable {N P:Side}(G:Ratio N P)
namespace TripD
variable (j:ℕ) {n:ℕ}
abbrev SetK (j:ℕ)(L:Side)(n:ℕ):Prop:=∀ t:Cover,n < Laurent.size t→tub (brix j L) t=0
lemma avail(L:Side)(p:Odd L.val): ∃ n,SetK j L n:=by obtain ⟨S,h⟩:=BasisRim.Sheet.sound L j p; exact ⟨S.sup Laurent.size,fun x u=>h _ (fun l=> not_le_of_gt u (le_sup l))⟩
-- pose inside integer reach. budget post-lambda.
def units (L:Side)(n:ℕ):ℕ:=16*L.val+8*L.val*n
def plot (S:Finset Cover) : Finset ℕ:=S.image names.symm
abbrev window (K:ℕ)(x:Site (More P)) : Set (Site (More P)) := {y| separation x y ≤ K}
structure Portray (G:Ratio N P)(i l:Iota G)(K:ℕ)(f:Bkg (More P)→ℂ) : Prop where
 cont:Continuous f
 localP: LocalOn (window (2*K) (portico G l.1)) f
 vista: K < separation (arrive G i.1) (portico G l.1) → f=0
variable {G} {i l:Iota G}{K:ℕ}
namespace Portray
variable {f g:Bkg (More P)→ℂ}
lemma null : Portray G i l K 0:= ⟨continuous_const,fun _ _ _=>rfl,fun _=>rfl⟩
lemma plus (p:Portray G i l K f)(h:Portray G i l K g): Portray G i l K (fun x=> f x+g x):= ⟨p.cont.add h.cont,fun V U v=>congrArg₂ (·+·) (p.localP V U v) (h.localP V U v),fun u=>funext fun y=>by rw [p.vista u,h.vista u]; simp⟩
lemma mint (p:Portray G i l K f)(r:ℂ): Portray G i l K (fun x=>r*f x):=⟨continuous_const.mul p.cont,fun V U v=>congrArg _ (p.localP V U v),fun v=>by rw [p.vista v]; funext; simp⟩
lemma pool{α:Type*}(S:Finset α)(F:α→ Bkg (More P)→ℂ)(h:∀ k∈S, Portray G i l K (F k)): Portray G i l K (fun x=>∑ k∈S,F k x):=by induction S using Finset.induction_on with| empty=>simp only [sum_empty]; exact null | insert a s e h'=>simp only [sum_insert e]; exact (h a (mem_insert_self ..)).plus (h' fun x t=>h x (mem_insert_of_mem t))
end Portray
variable (x:Bkg (More P))
-- data T depends ONLY on fine field
abbrev flag (N:Side)(x:Bkg (More P)):=unionP (x,(1:Bkg (More N)))
lemma flagP (w:Walk)(o:Site (More P))(c s:Slot) : Continuous fun V:Bkg (More P)=> (track (profile V) o w).1 c s:=by
 exact (((continuous_apply s).comp (continuous_apply c)).comp (((track_d o w).continuous.comp Dial.profile_c).fst))
variable (G) (ho:Odd G.count.val) (v:SetK j G.count n)
include ho v
lemma paint_t (a b:St G.count)(s:Cover)(o:Lattice.Order)(i l:Iota G) : Portray G i l (units G.count n) (fun x=> drag G true false a b s (tub (brix j G.count) s a b) o (flag N x) i l):=by
 rcases i with ⟨d,c⟩; rcases l with ⟨l,q⟩
 unfold drag; simp only [Matrix.sum_apply,panel]; apply Portray.pool; intro i _; let N':=units G.count n; let p':=(i,a); let t:=tub (brix j G.count) s a b; let q':=(i+ wrap N s,b); by_cases h:d=(i,a)∧l=(i+wrap N s,b); -- placeholder
 · obtain ⟨x,y⟩:=h; subst d; subst l; simp only [Matrix.of_apply,ite_true,and_self]; by_cases g: n < Laurent.size s
   · simp only [v s g, Matrix.zero_apply,mul_zero, zero_smul]; exact Portray.null
   let A:= arrive G (i,a); let B:= portico G q'; let U:= runD true false G.count a b s o; have he:stop A U=B:= worn G true false ho a b s o i; have hb: B ∈ visits A U:=by rw [←he]; exact List.mem_toFinset.mp (trace_last ..)
   have hx:U.length ≤ N':=(run_len ..).trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ (by omega)) _); have hv:separation A B ≤ N':=(Broc.visit_v A U B hb).trans hx
   refine Portray.mint (f:=fun V=> (track (profile V) A U).1 c q) ?_ (wind i s*t) -- tune t syntactic
   refine ⟨flagP ..,?_, fun q=>(not_le_of_gt q hv).elim⟩
   have h1(y)(u:y∈ visits A U): y∈ window (2*N') B:= (separation_triangle B A y).trans ((Nat.add_le_add (le_trans (le_of_eq (separation_comm ..)) hv) ((Broc.visit_v A U y u).trans hx)).trans (le_of_eq (by omega)))
   intro X Y e; change (track (profile X) A U).1 _ _=_; change _= (track (profile Y) A U).1 c q; rw [track_pr,track_pr]; rw [show travel X A U=travel Y A U from travel_local A U X Y (fun i u p=>e i (h1 _ u) (h1 _ p))]
 · simp only [Matrix.of_apply,h, ↓reduceIte];
   exact Portray.null
end TripD
end YM.CF.Peaks
