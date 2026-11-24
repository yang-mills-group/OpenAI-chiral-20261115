import YM.CF.Buffered.Shower
/-! # Film construction. The extension choices and reflections are at SAME μ. -/
set_option autoImplicit false
set_option synthInstance.maxSize 22000
set_option linter.unusedSectionVars false
set_option maxHeartbeats 480000
noncomputable section
namespace YM.CF.Buffered.Region
open Function Filter NormedSpace SU Lat Lattice Cube Finset Mir Mir.Trip Phase RP MeasureTheory Roost Rails Mil RG WilsonStartup Spark Nova Fock Push.SectorMeasure Ordered Cin Stripe Tile Traversed Stack Bays
open Installed (point)
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder Fin.NatCast
attribute [local instance] opCStarAlgebra
variable {m v p B n w:Side}{δ:Axis→Side}{i:Axis}{ζ:TStem i}
-- length argument not used at all in `stripF`.
variable {e x:ℝ} (K: Ticket m v B p e x) (Z:Car ζ→Badge v B) (q:Clip)(β u:ℝ) (p':Bool)
local notation "N" => n.val
local notation "C" => Car ζ
local notation "G" => GridM v B
local notation "S" => Locale v B
local notation "X" => Wet ζ v B
abbrev Wide (ζ:TStem i)(v B:Side):= Bays (Car ζ) (GridM v B)
local notation "A" => Wide ζ v B
abbrev EdgePorts (ζ:TStem i)(v B:Side):= Car ζ × Kid v B i
local notation "d" => EdgePorts ζ v B
local notation "O" => Stack.Cell X X
namespace Saddle
variable (s':Stack.Cell (Wet ζ v B) (Wet ζ v B))
def slip (p:Bool)(x:Stack.Cell X X) := host (chaired x p)
lemma slip_cont (i:C): Continuous fun x:O=> slip p' x i := (host_cont i).comp (chaired_cont p')
local notation "E" => slip p' s'

def space (s':O):ℂ:=∏ i:C, K.deck q β (slip p' s' i)
def markV (s':O): FC A := Rect.Badge.affix (wall _ _) Z (slip p' s')
def seedP (s':O): FC A := ∑ i:C, into (install _ i) (Tile.seed K (slip p' s' i))
def thorn (r:C)(z:C→ S) (j:Off i) : FC A:= tip r j • joinF j.val (install _ r) (install _ (Taxi r j)) (z r,z (Taxi r j))
def horn (s':O):FC A:= ∑ i:C,(into (install _ i) (pit (slip p' s' i))+ ∑ j, thorn i (slip p' s') j)
def waist (g:Bool)(k:d)(s':O): FC A:= into (install _ k.1) (if g then outgo i k.2 (slip p' s' k.1) else income i k.2 (slip p' s' k.1))
lemma settle_core : Sector univ false (horn p' s'):=Sector.sumS _ _ (fun r _=> (uninstall _ (pit_sector ..)).add (Sector.sumS _ _ (fun j _=> Heat.sector_real _ (join_local ..))))
lemma settle_exp : Sector univ false (exp (seedP K p' s')):= Heat.sector_exp (Sector.sumS _ _ (fun r _=>uninstall _ (Tile.seed_sector ..)))
lemma settle_side (g:Bool)(r:d) : Sector univ true (waist p' g r s'):=by
 unfold waist; split; exact uninstall _ (outs_sector ..); exact uninstall _ (ins_sector ..)
lemma spaces : Envelope (space (ζ:=ζ) K q β p'):= product_env _ _ (fun i _=> Env.along (g:=fun x:O=> slip p' x i) (K.deck_ok ..) (slip_cont p' i).measurable)
lemma marks : Envelope (markV Z p'):= Rect.Badge.affix_env _ Z _ (fun i=>(slip_cont p' i).measurable)
lemma seeds : Envelope (fun x:O=> exp (seedP K p' x)):=by
 letI : NormedAlgebra ℚ (FC A):=NormedAlgebra.restrictScalars ℚ ℝ _; exact Girt.pole_w (seedP K p') exp exp_continuous (show Envelope (seedP (ζ:=ζ) K p') from Env.total _ (fun i=> Girt.pole_w _ _ (into_cont _) (Env.along (g:=fun x:O=> slip p' x i) (Tile.seed_paid K) (slip_cont p' i).measurable)))
lemma horns : Continuous (horn (ζ:=ζ) (v:=v) (B:=B) p'):=continuous_finsetSum _ fun i _=> ((into_cont _).comp (pit_cont.comp (slip_cont p' i))).add (continuous_finsetSum _ (fun j _=> ((join_cont ..).comp ((slip_cont p' i).prodMk (slip_cont p' (Taxi i j)))).const_smul (tip i j))) -- tune not syntactic
lemma waists (g:Bool)(r:d) : Continuous (waist p' g r):=by unfold waist; cases g; exact (into_cont _).comp ((legs_cont ..).2.comp (slip_cont p' r.1)); exact (into_cont _).comp ((legs_cont ..).1.comp (slip_cont p' r.1))
lemma sparse (j k:d)(w:O) : waist p' false j w * waist p' true k w= -(waist p' true k w * waist p' false j w):= by
 obtain ⟨j,a⟩:=j; obtain ⟨k,b⟩:=k; unfold waist; dsimp only; rw [if_pos rfl,if_neg (by decide)]; by_cases e:j=k
 · subst k; rw [←map_mul, ←map_mul, leg_swap i, map_neg]
 simpa only [Sector.grainB,Bool.and_true,ite_true,neg_smul,one_smul] using Sector.apart (sector_in _ (ins_sector i a (slip p' w j))) (sector_in _ (outs_sector i b (slip p' w k))) (Installed.apart (wall C G) (show j≠k from e)) -- tune

def printF : Film X X d A where
 weight:=space K q β p'
 mark:=markV Z p'
 seed x:= exp (seedP K p' x)
 core x:= u • horn p' x
 side h i x:= Real.sqrt u • waist p' h i x
 regularA:= spaces K .. -- tune
 regularB:=marks ..
 regularC:=seeds ..
 regularD:=(horns p').const_smul u
 regularE b k:=(waists p' b k).const_smul (Real.sqrt u)
 sectorM _:=Rect.Badge.affix_state ..
 sectorV _:=settle_exp ..
 sectorC _:=Heat.sector_real _ (settle_core ..)
 sectorS b i z:= Heat.sector_real _ (settle_side ..)
 sparse z i j:=by rw [Algebra.smul_mul_assoc,Algebra.mul_smul_comm,Algebra.smul_mul_assoc,Algebra.mul_smul_comm, Saddle.sparse p' i j,smul_neg,smul_neg]

def unitTurn (ζ:TStem i)(v B:Side): UNI (Wide ζ v B):= Installed.uniform (wall _ _) (Equiv.refl _) (turnF i _ _)
def upper (ζ:TStem i)(v B:Side):Finset (Wide ζ v B):= Installed.filled (wall _ _) (Tile.sky v B)
local notation "U" => unitTurn ζ v B
local notation "Z'" => slip (!p') (mirrorCell X X s')
lemma upper_v : twist U (cutM (upper ζ v B)ᶜ)=cutM (upper ζ v B):= Installed.uniform_flip _ _ _ _ (Installed.uniform_flip _ _ _ _ (above_grade i)) -- tune
lemma headed (u:C): Framed (install G u) (install G u) U (turnF i v B) := Installed.uniform_frame _ (Equiv.refl _) (turnF i v B) u
lemma switched (r:C): Z' r= Rails.past {i} (E r):= by
 cases p'
 · change host ((mirrorCell X X s').1, shell s'.2) r= Rails.past {i} (host s' r); exact host_mirror ..
 let x:Stack.Cell X X:=(s'.1,shell s'.2); have he:= host_mirror r (mirrorCell X X x); rw [show shell (mirrorCell X X x).2=s'.2 from shell_one s'.2] at he; exact he
lemma backwards (V:Traversed ζ δ n) (t:Landing δ)(F: C→ Badge v B)(v':∀ (r: Car ζ) z, (F r).label (Rails.past {i} z) = theta (turnF i v B) ((Z r).label z)) : Film.Reversed (printF K Z q β u p') (printF K F q β u (!p')) U:=by
 constructor
 · intro x; change space K q β (!p') _=star (space K q β p' x); unfold space; rw [star_prod]; refine prod_congr rfl fun i _=>?_ ; simp_rw [switched, Ticket.deck_star] -- tune name
 · intro z; change u • horn (!p') _=theta _ (u • horn p' z); rw [theta_rsmul]; apply congrArg; unfold horn; simp_rw [theta_sum,theta_add,theta_sum]; apply sum_congr rfl; intro r _; rw [(headed r).theta _ (pit_sector ..),switched, pit_turn]; apply congrArg; apply sum_congr rfl; intro j _; unfold thorn; rw [theta_rsmul,switched,switched, Tile.join_turn j.val i _ _ _ _ (headed _) (headed _) (Installed.apart (wall C G) (V.many_pal t 0 r j).symm) j.property] -- tune implicit orders
 · intro z; change markV F (!p') (mirrorCell _ _ z)=theta U (markV Z p' z); unfold markV Rect.Badge.affix; let f : FC A→* FC A:=⟨⟨theta U,theta_one _⟩,theta_mul _⟩; symm
   apply pal_trans (h:=f); intro r _; unfold Rect.Badge.one; rw [switched,v']; exact (headed r).theta _ ((Z r).state _)
 · intro z; change exp (seedP K (!p') _)=theta U (exp (seedP K p' z)); rw [←Heat.theta_exp]; apply congrArg; unfold seedP; rw [theta_sum]; refine sum_congr rfl fun v _=>?_ ; rw [switched,Tile.seed_refl, (headed v).theta _ (Tile.seed_sector ..)]
 · intro b k z; change Real.sqrt u • waist (!p') (!b) k _=theta U (Real.sqrt u • waist p' b k z); rw [theta_rsmul]; unfold waist; rw [switched]; cases b
   · rw [Bool.not_false,if_pos rfl,if_neg (by decide), outlook, (headed k.1).theta _ (ins_sector ..)]
   rw [Bool.not_true,if_pos rfl,if_neg (by decide), inch,(headed k.1).theta _ (outs_sector ..)]
end Saddle
end YM.CF.Buffered.Region
#print axioms YM.CF.Buffered.Region.Saddle.backwards
#print YM.CF.Buffered.Region.Saddle.printF
