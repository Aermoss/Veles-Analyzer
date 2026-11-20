import * as vscode from "vscode";
import { execFile } from "node:child_process";
import { createHash } from "node:crypto";
import * as fs from "node:fs";
import * as os from "node:os";
import * as path from "node:path";

const IDENTIFIER = "[A-Za-z_][A-Za-z0-9_]*";
const DIAGNOSTIC_PATTERN = /^(.*):(\d+):(\d+): (Error|Fatal Error|Warning|Info): (.+)$/;
const ANSI_ESCAPE = /\x1B(?:[@-Z\\-_]|\[[0-?]*[ -/]*[@-~])/g;
const BIT_VECTOR = /^([ui])([1-9][0-9]*)$/;

const KEYWORD_DOCS: Record<string, string> = {
    module: "Declares a hardware module with a port list and a body.",
    extern: "Declares a module that already exists in SystemVerilog, such as a vendor primitive. Nothing is emitted for it.",
    enum: "Declares an enumeration. Its width is inferred from the variants unless a base type such as `: u4` is given.",
    type: "Declares a type alias, for example `type Word = u32;`.",
    const: "Declares a compile-time constant that can be used in expressions, widths and memory lengths.",
    let: "Declares a named combinational value. A `let` whose value is `Module { ... }` declares an instance.",
    wire: "Declares a combinational signal that is driven separately, by a `comb` block or a continuous assignment.",
    reg: "Declares a register. Its initial value becomes the reset value. Registers are assigned in `seq` blocks with `<-`.",
    in: "Input port. Also separates the variable from the range in `for i in 0..N`.",
    out: "Output port. `out reg` declares a registered output.",
    inout: "Bidirectional port. It can only be connected to an `inout` port of an instance.",
    seq: "Sequential block, emitted as `always_ff`. Uses the module's first clock and reset unless `seq(clk)` or `seq(clk, rst)` is given. Assign with `<-`.",
    comb: "Combinational block, emitted as `always_comb`. Assign with `=`; every signal it drives must be assigned on every path.",
    if: "Conditional statement or expression. The condition must be a `bool`. When it is a constant, only the chosen branch is checked and emitted. At module level `if CONSTANT { ... }` keeps only the items of the chosen branch.",
    for: "Repeats its body for each value of a constant range, `for i in 0..N { ... }`. Inside `comb` and `seq` blocks it repeats statements. At module level it repeats items: every signal or instance declared inside becomes an array, the current element inside the loop and `name[k]` everywhere, emitted as `name_k`.",
    else: "Alternative branch of an `if`.",
    match: "Compares a value against constant patterns; emitted as a `case` statement. `_` matches anything.",
    as: "Cast: truncates, zero-extends, sign-extends or reinterprets a value, for example `x as u16`.",
    true: "The `bool` value 1.",
    false: "The `bool` value 0."
};

const TYPE_DOCS: Record<string, string> = {
    bool: "1-bit unsigned value, the same type as `u1`.",
    clock: "Clock signal. Registers update on its rising edge.",
    reset: "Asynchronous, active-high reset. It can be read as a `bool`."
};

interface Builtin {
    label: string;
    parameters: string[];
    documentation: string;
}

const BUILTINS: Record<string, Builtin> = {
    cat: { label: "cat(values...) -> u<total width>", parameters: ["values..."], documentation: "Concatenates bit vectors. The first argument becomes the most significant part." },
    rep: { label: "rep(count, value) -> u<count * width>", parameters: ["count", "value"], documentation: "Repeats `value` `count` times. `count` must be a constant." },
    any: { label: "any(value) -> bool", parameters: ["value"], documentation: "OR reduction: true if any bit is set." },
    all: { label: "all(value) -> bool", parameters: ["value"], documentation: "AND reduction: true if every bit is set." },
    parity: { label: "parity(value) -> bool", parameters: ["value"], documentation: "XOR reduction: true if an odd number of bits is set." },
    clog2: { label: "clog2(n) -> integer", parameters: ["n"], documentation: "Ceiling of log2(n), evaluated at compile time." }
};

const KEYWORDS = Object.keys(KEYWORD_DOCS);
const TYPES = ["bool", "clock", "reset", "u1", "u2", "u4", "u8", "u16", "u32", "u64", "i8", "i16", "i32", "i64"];

type DeclarationKind = "module" | "enum" | "variant" | "const" | "type" | "port" | "let" | "wire" | "reg" | "instance";

interface Declaration {
    name: string;
    kind: DeclarationKind;
    uri: vscode.Uri;
    start: number;
    end: number;
    nameStart: number;
    text: string;
    documentation?: string;
    container?: Declaration;
    external?: boolean;
    parameters?: string[];
    input?: boolean;
    module?: string;
    children: Declaration[];
}

interface FileIndex {
    uri: vscode.Uri;
    declarations: Declaration[];
}

function executableFile(name: string): boolean {
    try {
        return fs.statSync(name).isFile();
    } catch {
        return false;
    }
}

function maskNonCode(source: string): string {
    const mask = (value: string): string => value.replace(/[^\r\n]/g, " ");
    return source.replace(/"(?:\\.|[^"\\\r\n])*"?|\/\*[\s\S]*?(?:\*\/|$)|\/\/[^\r\n]*/g, mask);
}

function collapse(text: string, limit = 240): string {
    const value = text.replace(/\s+/g, " ").trim();
    return value.length > limit ? `${value.slice(0, limit - 3)}...` : value;
}

function findMatching(code: string, open: number): number {
    const pairs: Record<string, string> = { "(": ")", "[": "]", "{": "}" };
    const stack: string[] = [];

    for (let i = open; i < code.length; i++) {
        const character = code[i];
        if (pairs[character]) stack.push(pairs[character]);
        else if (character === ")" || character === "]" || character === "}") {
            if (stack.pop() !== character) return -1;
            if (stack.length === 0) return i;
        }
    }

    return -1;
}

function splitTopLevel(code: string, start: number, end: number): Array<{ start: number; end: number }> {
    const parts: Array<{ start: number; end: number }> = [];
    let depth = 0;
    let partStart = start;

    for (let i = start; i < end; i++) {
        const character = code[i];
        if (character === "(" || character === "[" || character === "{" || character === "<") depth++;
        else if (character === ")" || character === "]" || character === "}" || character === ">") depth = Math.max(0, depth - 1);
        else if (character === "," && depth === 0) {
            parts.push({ start: partStart, end: i });
            partStart = i + 1;
        }
    }

    if (code.slice(partStart, end).trim()) parts.push({ start: partStart, end });
    return parts;
}

function statementEnd(code: string, start: number): number {
    let depth = 0;

    for (let i = start; i < code.length; i++) {
        const character = code[i];
        if (character === "(" || character === "[" || character === "{") depth++;
        else if (character === ")" || character === "]" || character === "}") {
            if (depth === 0) return i;
            depth--;
        } else if (character === ";" && depth === 0) return i + 1;
    }

    return code.length;
}

function parseInteger(text: string): number | undefined {
    const value = text.replace(/_/g, "").trim();
    if (/^0[xX][0-9a-fA-F]+$/.test(value)) return parseInt(value.slice(2), 16);
    if (/^0[bB][01]+$/.test(value)) return parseInt(value.slice(2), 2);
    if (/^0[oO][0-7]+$/.test(value)) return parseInt(value.slice(2), 8);
    if (/^[0-9]+$/.test(value)) return parseInt(value, 10);
    return undefined;
}

function documentationAbove(source: string, offset: number): string | undefined {
    const lines = source.slice(0, offset).split(/\r\n|\r|\n/);
    const result: string[] = [];

    for (let line = lines.length - 2; line >= 0; line--) {
        const text = lines[line].trim();
        if (!text.startsWith("//")) break;
        result.unshift(text.replace(/^\/\/+\s?/, ""));
    }

    return result.length ? result.join("\n") : undefined;
}

function indexSource(uri: vscode.Uri, source: string): FileIndex {
    const code = maskNonCode(source);
    const declarations: Declaration[] = [];
    const modules: Declaration[] = [];
    const portLists: Array<{ start: number; end: number }> = [];

    const make = (kind: DeclarationKind, name: string, nameStart: number, start: number, end: number, text: string): Declaration =>
        ({ name, kind, uri, start, end, nameStart, text, children: [] });

    const moduleAt = (offset: number): Declaration | undefined =>
        modules.find(module => !module.external && offset > module.start && offset < module.end);

    const modulePattern = new RegExp(`\\b(extern\\s+)?module\\s+(${IDENTIFIER})\\s*(?:<([^>]*)>\\s*)?\\(`, "g");
    let match: RegExpExecArray | null;

    while ((match = modulePattern.exec(code)) !== null) {
        const open = modulePattern.lastIndex - 1;
        const close = findMatching(code, open);
        if (close < 0) continue;
        const external = Boolean(match[1]);
        portLists.push({ start: open, end: close });
        const nameStart = match.index + match[0].indexOf(match[2], match[1] ? match[1].length + 6 : 6);
        let end = close + 1;

        if (!external) {
            const brace = code.slice(close + 1).search(/\S/);
            if (brace >= 0 && code[close + 1 + brace] === "{") {
                const bodyEnd = findMatching(code, close + 1 + brace);
                end = bodyEnd < 0 ? code.length : bodyEnd + 1;
            }
        } else {
            end = statementEnd(code, close + 1);
        }

        const module = make("module", match[2], nameStart, match.index, end, "");
        module.external = external;
        module.parameters = match[3] ? match[3].split(",").map(parameter => parameter.trim()).filter(parameter => parameter.length > 0) : [];
        module.documentation = documentationAbove(source, match.index);
        const portTexts: string[] = [];

        for (const part of splitTopLevel(code, open + 1, close)) {
            const text = code.slice(part.start, part.end);
            const port = new RegExp(`^\\s*(${IDENTIFIER})\\s*:\\s*(inout|in|out)\\b`).exec(text);
            if (!port) continue;
            const portStart = part.start + text.indexOf(port[1]);
            const declaration = make("port", port[1], portStart, portStart, part.end, collapse(text));
            declaration.input = port[2] !== "out";
            declaration.container = module;
            module.children.push(declaration);
            portTexts.push(declaration.text);
        }

        const header = `${external ? "extern " : ""}module ${match[2]}${module.parameters.length ? `<${module.parameters.join(", ")}>` : ""}`;
        module.text = portTexts.length ? `${header}(\n    ${portTexts.join(",\n    ")}\n)` : `${header}()`;
        modules.push(module);
        declarations.push(module);
        modulePattern.lastIndex = close + 1;
    }

    const enumPattern = new RegExp(`\\benum\\s+(${IDENTIFIER})\\s*(?::\\s*([^{;]*?))?\\s*\\{`, "g");

    while ((match = enumPattern.exec(code)) !== null) {
        const open = enumPattern.lastIndex - 1;
        const close = findMatching(code, open);
        if (close < 0) continue;
        const nameStart = match.index + match[0].indexOf(match[1], 4);
        const enumeration = make("enum", match[1], nameStart, match.index, close + 1, "");
        enumeration.documentation = documentationAbove(source, match.index);
        enumeration.container = moduleAt(match.index);
        const names: string[] = [];
        let next: number | undefined = 0;

        for (const part of splitTopLevel(code, open + 1, close)) {
            const text = code.slice(part.start, part.end);
            const variant = new RegExp(`^\\s*(${IDENTIFIER})\\s*(?:=\\s*([\\s\\S]+))?$`).exec(text);
            if (!variant) continue;
            const value: number | undefined = variant[2] !== undefined ? parseInteger(variant[2]) : next;
            next = value === undefined ? undefined : value + 1;
            const variantStart = part.start + text.indexOf(variant[1]);
            const description = `${match[1]}::${variant[1]}${value === undefined ? "" : ` = ${value}`}`;
            const declaration = make("variant", variant[1], variantStart, variantStart, part.end, description);
            declaration.container = enumeration;
            enumeration.children.push(declaration);
            names.push(variant[1]);
        }

        const base = match[2]?.trim();
        enumeration.text = `enum ${match[1]}${base ? `: ${base}` : ""} { ${names.join(", ")} }`;
        declarations.push(enumeration);
        if (enumeration.container) enumeration.container.children.push(enumeration);
    }

    const namedPattern = new RegExp(`\\b(const|type|let|wire|reg)\\s+(${IDENTIFIER})`, "g");

    while ((match = namedPattern.exec(code)) !== null) {
        const offset = match.index;
        if (portLists.some(list => offset > list.start && offset < list.end)) continue;
        const end = statementEnd(code, namedPattern.lastIndex);
        const nameStart = match.index + match[0].lastIndexOf(match[2]);
        let kind = match[1] as DeclarationKind;
        const declaration = make(kind, match[2], nameStart, match.index, end, collapse(code.slice(match.index, end)));
        declaration.documentation = documentationAbove(source, match.index);
        declaration.container = moduleAt(match.index);

        if (kind === "let") {
            const instance = new RegExp(`^\\s*=\\s*(${IDENTIFIER})\\s*(?:<[^>]*>\\s*)?\\{`).exec(code.slice(namedPattern.lastIndex, end));

            if (instance && instance[1] !== "if") {
                kind = "instance";
                declaration.kind = kind;
                declaration.module = instance[1];
                declaration.text = `let ${match[2]} = ${instance[1]} { ... }`;
            }
        }

        declarations.push(declaration);
        if (declaration.container) declaration.container.children.push(declaration);
    }

    return { uri, declarations };
}

function positionAt(document: vscode.TextDocument, offset: number): vscode.Position {
    return document.positionAt(offset);
}

function symbolKind(kind: DeclarationKind): vscode.SymbolKind {
    switch (kind) {
        case "module": return vscode.SymbolKind.Module;
        case "enum": return vscode.SymbolKind.Enum;
        case "variant": return vscode.SymbolKind.EnumMember;
        case "const": return vscode.SymbolKind.Constant;
        case "type": return vscode.SymbolKind.TypeParameter;
        case "port": return vscode.SymbolKind.Field;
        case "instance": return vscode.SymbolKind.Object;
        default: return vscode.SymbolKind.Variable;
    }
}

function completionKind(kind: DeclarationKind): vscode.CompletionItemKind {
    switch (kind) {
        case "module": return vscode.CompletionItemKind.Module;
        case "enum": return vscode.CompletionItemKind.Enum;
        case "variant": return vscode.CompletionItemKind.EnumMember;
        case "const": return vscode.CompletionItemKind.Constant;
        case "type": return vscode.CompletionItemKind.TypeParameter;
        case "port": return vscode.CompletionItemKind.Field;
        case "instance": return vscode.CompletionItemKind.Module;
        default: return vscode.CompletionItemKind.Variable;
    }
}

function builtinTypeDoc(word: string): string | undefined {
    if (TYPE_DOCS[word]) return TYPE_DOCS[word];
    const bits = BIT_VECTOR.exec(word);
    if (!bits) return undefined;
    return `${bits[2]}-bit ${bits[1] === "u" ? "unsigned" : "signed"} bit vector.`;
}

function findActiveCall(code: string, offset: number): { name: string; activeParameter: number } | undefined {
    const stack: Array<{ open: number; commas: number }> = [];

    for (let i = 0; i < Math.min(offset, code.length); i++) {
        if (code[i] === "(") stack.push({ open: i, commas: 0 });
        else if (code[i] === ")") stack.pop();
        else if (code[i] === "," && stack.length) stack[stack.length - 1].commas++;
    }

    const active = stack[stack.length - 1];
    if (!active) return undefined;
    const name = new RegExp(`(${IDENTIFIER})\\s*$`).exec(code.slice(0, active.open))?.[1];
    return name ? { name, activeParameter: active.commas } : undefined;
}

function findIncludes(source: string): Array<{ name: string; start: number; end: number }> {
    const code = maskNonCode(source);
    const results: Array<{ name: string; start: number; end: number }> = [];
    const directive = /#\[\s*include\b/g;
    let match: RegExpExecArray | null;

    while ((match = directive.exec(code)) !== null) {
        const close = code.indexOf("]", directive.lastIndex);
        const end = close < 0 ? code.length : close;
        const strings = /"((?:\\.|[^"\\\r\n])*)"/g;
        strings.lastIndex = directive.lastIndex;
        let literal: RegExpExecArray | null;

        while ((literal = strings.exec(source)) !== null && literal.index < end) {
            results.push({ name: literal[1].replace(/\\(.)/g, "$1"), start: literal.index + 1, end: literal.index + 1 + literal[1].length });
        }

        directive.lastIndex = end;
    }

    return results;
}

function samePath(a: string, b: string): boolean {
    return path.resolve(a).toLowerCase() === path.resolve(b).toLowerCase();
}

export function activate(context: vscode.ExtensionContext): void {
    const diagnostics = vscode.languages.createDiagnosticCollection("veles");
    const timers = new Map<string, ReturnType<typeof setTimeout>>();
    const generations = new Map<string, number>();
    const output = vscode.window.createOutputChannel("Veles");
    let workspaceIndex: Map<string, FileIndex> | undefined;
    let workspaceIndexBuild: Promise<Map<string, FileIndex>> | undefined;
    let workspaceIndexRevision = 0;
    let lastReportedCompilerIssue: string | undefined;
    let contentsSupported = true;

    const selector = { scheme: "file", language: "veles" };
    context.subscriptions.push(diagnostics, output, {
        dispose() {
            for (const timer of timers.values()) clearTimeout(timer);
            timers.clear();
        }
    });

    function reportCompilerIssue(key: string, message: string): void {
        if (lastReportedCompilerIssue === key) return;
        lastReportedCompilerIssue = key;
        void vscode.window.showErrorMessage(message);
    }

    function findCompiler(folder: vscode.WorkspaceFolder | undefined): string | undefined {
        const configured = vscode.workspace.getConfiguration("veles", folder?.uri).get<string>("compilerPath");
        const candidates: string[] = [];
        if (configured) candidates.push(path.resolve(folder?.uri.fsPath || "", configured));
        const names = process.platform === "win32" ? ["velesc.exe", "velesc"] : ["velesc", "velesc.exe"];

        for (const entry of (process.env.PATH || "").split(path.delimiter).filter(Boolean)) {
            for (const name of names) candidates.push(path.join(entry, name));
        }

        for (const root of [folder, ...(vscode.workspace.workspaceFolders || [])]) {
            if (!root) continue;
            for (const name of names) {
                candidates.push(path.join(root.uri.fsPath, "bin", name));
                candidates.push(path.resolve(root.uri.fsPath, "..", "Veles", "bin", name));
            }
        }

        return candidates.find(executableFile);
    }

    function includePaths(folder: vscode.WorkspaceFolder | undefined): string[] {
        const configured = vscode.workspace.getConfiguration("veles", folder?.uri).get<string[]>("includePaths") || [];
        return configured.filter(Boolean).map(entry => path.resolve(folder?.uri.fsPath || "", entry));
    }

    function resolveInclude(name: string, document: vscode.TextDocument): string | undefined {
        const folder = vscode.workspace.getWorkspaceFolder(document.uri);
        const directories = [path.dirname(document.uri.fsPath), ...includePaths(folder)];

        for (const directory of directories) {
            const candidate = path.resolve(directory, name);
            if (executableFile(candidate)) return candidate;
        }

        return undefined;
    }

    function invalidateIndex(): void {
        workspaceIndexRevision++;
        workspaceIndex = undefined;
    }

    async function getWorkspaceIndex(): Promise<Map<string, FileIndex>> {
        if (workspaceIndex) return workspaceIndex;
        if (workspaceIndexBuild) return workspaceIndexBuild;
        const revision = workspaceIndexRevision;

        workspaceIndexBuild = (async () => {
            const uris = new Map<string, vscode.Uri>();
            const excluded = "{**/.claude/**,**/.git/**,**/node_modules/**}";

            for (const uri of await vscode.workspace.findFiles("**/*.vel", excluded)) uris.set(uri.toString(), uri);

            for (const folder of vscode.workspace.workspaceFolders || []) {
                for (const include of includePaths(folder)) {
                    for (const uri of await vscode.workspace.findFiles(new vscode.RelativePattern(vscode.Uri.file(include), "**/*.vel"), excluded)) {
                        uris.set(uri.toString(), uri);
                    }
                }
            }

            for (const document of vscode.workspace.textDocuments) {
                if (document.languageId === "veles" && document.uri.scheme === "file") uris.set(document.uri.toString(), document.uri);
            }

            const open = new Map(vscode.workspace.textDocuments.map(document => [document.uri.toString(), document]));
            const index = new Map<string, FileIndex>();

            for (const uri of uris.values()) {
                let source: string;

                try {
                    const document = open.get(uri.toString());
                    source = document ? document.getText() : Buffer.from(await vscode.workspace.fs.readFile(uri)).toString("utf8");
                } catch {
                    continue;
                }

                index.set(uri.toString(), indexSource(uri, source));
            }

            if (revision === workspaceIndexRevision) workspaceIndex = index;
            return index;
        })().finally(() => {
            workspaceIndexBuild = undefined;
        });

        return workspaceIndexBuild;
    }

    async function indexesFor(document: vscode.TextDocument): Promise<FileIndex[]> {
        const current = indexSource(document.uri, document.getText());
        const others = [...(await getWorkspaceIndex()).values()].filter(index => index.uri.toString() !== document.uri.toString());
        return [current, ...others];
    }

    function globals(indexes: FileIndex[], name?: string): Declaration[] {
        const result: Declaration[] = [];

        for (const index of indexes) {
            for (const declaration of index.declarations) {
                if (declaration.container || declaration.kind === "port" || declaration.kind === "variant") continue;
                if (name === undefined || declaration.name === name) result.push(declaration);
            }
        }

        return result;
    }

    function findModule(indexes: FileIndex[], name: string): Declaration | undefined {
        return globals(indexes, name).find(declaration => declaration.kind === "module");
    }

    function findEnum(indexes: FileIndex[], name: string, scope?: Declaration): Declaration | undefined {
        const local = scope?.children.find(child => child.kind === "enum" && child.name === name);
        return local || globals(indexes, name).find(declaration => declaration.kind === "enum");
    }

    function enclosingModule(index: FileIndex, offset: number): Declaration | undefined {
        return index.declarations.find(declaration => declaration.kind === "module" && !declaration.external && offset > declaration.start && offset < declaration.end);
    }

    interface Context {
        word: string;
        range: vscode.Range;
        offset: number;
        code: string;
        index: FileIndex;
        indexes: FileIndex[];
        module?: Declaration;
    }

    async function contextAt(document: vscode.TextDocument, position: vscode.Position): Promise<Context | undefined> {
        const range = document.getWordRangeAtPosition(position, /[A-Za-z_][A-Za-z0-9_]*/);
        const offset = document.offsetAt(range ? range.start : position);
        const indexes = await indexesFor(document);
        const index = indexes[0];
        const code = maskNonCode(document.getText());
        if (code[offset] === " " && range) return undefined;
        return { word: range ? document.getText(range) : "", range: range || new vscode.Range(position, position), offset, code, index, indexes, module: enclosingModule(index, offset) };
    }

    function enumPrefix(context: Context): string | undefined {
        return new RegExp(`(${IDENTIFIER})\\s*::\\s*$`).exec(context.code.slice(0, context.offset))?.[1];
    }

    function memberPrefix(context: Context): string | undefined {
        return new RegExp(`(${IDENTIFIER})\\s*(?:\\[[^\\[\\]]*\\]\\s*)*\\.\\s*$`).exec(context.code.slice(0, context.offset))?.[1];
    }

    function instanceLiteral(context: Context): Declaration | undefined {
        const before = context.code.slice(0, context.offset);
        if (!/[{,]\s*$/.test(before)) return undefined;
        let depth = 0;

        for (let i = context.offset - 1; i >= 0; i--) {
            const character = context.code[i];
            if (character === "}" || character === ")" || character === "]") depth++;
            else if (character === "(" || character === "[") {
                if (depth === 0) return undefined;
                depth--;
            } else if (character === "{") {
                if (depth > 0) {
                    depth--;
                    continue;
                }

                const name = new RegExp(`=\\s*(${IDENTIFIER})\\s*(?:<[^>]*>\\s*)?$`).exec(context.code.slice(0, i))?.[1];
                return name ? findModule(context.indexes, name) : undefined;
            }
        }

        return undefined;
    }

    function parameterList(context: Context): Declaration | undefined {
        const match = new RegExp(`=\\s*(${IDENTIFIER})\\s*<[^<>{};]*$`).exec(context.code.slice(0, context.offset));
        if (!match || !/[<,]\s*$/.test(context.code.slice(0, context.offset))) return undefined;
        return findModule(context.indexes, match[1]);
    }

    function instanceModule(context: Context, name: string): Declaration | undefined {
        const instance = context.module?.children.find(child => child.kind === "instance" && child.name === name);
        return instance?.module ? findModule(context.indexes, instance.module) : undefined;
    }

    function resolve(context: Context): Declaration[] {
        const word = context.word;
        if (!word) return [];
        const enumName = enumPrefix(context);

        if (enumName) {
            const variant = findEnum(context.indexes, enumName, context.module)?.children.find(child => child.name === word);
            return variant ? [variant] : [];
        }

        const instanceName = memberPrefix(context);

        if (instanceName) {
            const port = instanceModule(context, instanceName)?.children.find(child => child.kind === "port" && child.name === word);
            return port ? [port] : [];
        }

        const literal = instanceLiteral(context);
        const literalPort = literal?.children.find(child => child.kind === "port" && child.name === word);
        if (literalPort && /^\s*[:,}]/.test(context.code.slice(context.offset + word.length))) return [literalPort];

        const local = context.module?.children.filter(child => child.name === word && child.kind !== "variant") || [];
        if (local.length) return local;
        return globals(context.indexes, word);
    }

    function hoverMarkdown(declaration: Declaration, context: Context): vscode.MarkdownString {
        const markdown = new vscode.MarkdownString();
        markdown.appendCodeblock(declaration.text, "veles");

        if (declaration.kind === "port" && declaration.container) {
            markdown.appendMarkdown(`\n${declaration.input ? "Input" : "Output"} of \`${declaration.container.name}\``);
        }

        if (declaration.kind === "instance" && declaration.module) {
            const module = findModule(context.indexes, declaration.module);
            if (module) markdown.appendCodeblock(module.text, "veles");
        }

        if (declaration.documentation) markdown.appendMarkdown(`\n\n${declaration.documentation}`);
        return markdown;
    }

    context.subscriptions.push(vscode.languages.registerHoverProvider(selector, {
        async provideHover(document, position) {
            const context = await contextAt(document, position);
            if (!context || !context.word) return undefined;
            const word = context.word;
            const resolved = resolve(context);

            if (resolved.length) {
                const markdown = new vscode.MarkdownString();

                resolved.slice(0, 4).forEach((declaration, index) => {
                    if (index) markdown.appendMarkdown("\n\n---\n\n");
                    markdown.appendMarkdown(hoverMarkdown(declaration, context).value);
                });

                return new vscode.Hover(markdown, context.range);
            }

            const builtin = BUILTINS[word];

            if (builtin) {
                const markdown = new vscode.MarkdownString();
                markdown.appendCodeblock(builtin.label, "veles");
                markdown.appendMarkdown(builtin.documentation);
                return new vscode.Hover(markdown, context.range);
            }

            const description = builtinTypeDoc(word) || KEYWORD_DOCS[word];
            return description ? new vscode.Hover(new vscode.MarkdownString(description), context.range) : undefined;
        }
    }));

    context.subscriptions.push(vscode.languages.registerDefinitionProvider(selector, {
        async provideDefinition(document, position) {
            const context = await contextAt(document, position);
            if (!context) return undefined;
            const locations: vscode.Location[] = [];

            for (const declaration of resolve(context)) {
                const target = declaration.uri.toString() === document.uri.toString()
                    ? document
                    : await vscode.workspace.openTextDocument(declaration.uri);
                const start = positionAt(target, declaration.nameStart);
                locations.push(new vscode.Location(declaration.uri, new vscode.Range(start, start.translate(0, declaration.name.length))));
            }

            return locations.length ? locations : undefined;
        }
    }));

    function declarationItem(declaration: Declaration, sortPrefix: string): vscode.CompletionItem {
        const item = new vscode.CompletionItem(declaration.name, completionKind(declaration.kind));
        item.detail = declaration.text.split("\n")[0];
        const documentation = new vscode.MarkdownString();
        documentation.appendCodeblock(declaration.text, "veles");
        if (declaration.documentation) documentation.appendMarkdown(`\n${declaration.documentation}`);
        item.documentation = documentation;
        item.sortText = `${sortPrefix}_${declaration.name}`;
        return item;
    }

    context.subscriptions.push(vscode.languages.registerCompletionItemProvider(selector, {
        async provideCompletionItems(document, position, token, completion) {
            const context = await contextAt(document, position);
            if (!context) return undefined;
            const parameterModule = parameterList(context);
            if ((completion.triggerCharacter === "<" || completion.triggerCharacter === ",") && !parameterModule && !instanceLiteral(context)) return undefined;
            const enumName = enumPrefix(context);

            if (enumName) {
                const enumeration = findEnum(context.indexes, enumName, context.module);
                return enumeration?.children.map((variant, index) => declarationItem(variant, `0_${String(index).padStart(4, "0")}`)) || [];
            }

            const instanceName = memberPrefix(context);

            if (instanceName) {
                const module = instanceModule(context, instanceName);
                return module?.children.filter(port => port.kind === "port" && !port.input).map((port, index) => declarationItem(port, `0_${String(index).padStart(4, "0")}`)) || [];
            }

            if (parameterModule) {
                return (parameterModule.parameters || []).map((parameter, index) => {
                    const item = new vscode.CompletionItem(parameter, vscode.CompletionItemKind.TypeParameter);
                    item.detail = `parameter of ${parameterModule.name}`;
                    item.insertText = new vscode.SnippetString(`${parameter}: $0`);
                    item.sortText = `0_${String(index).padStart(4, "0")}`;
                    return item;
                });
            }

            const literal = instanceLiteral(context);

            if (literal) {
                return literal.children.filter(port => port.kind === "port" && port.input).map((port, index) => {
                    const item = declarationItem(port, `0_${String(index).padStart(4, "0")}`);
                    item.insertText = new vscode.SnippetString(`${port.name}: $0`);
                    return item;
                });
            }

            const items: vscode.CompletionItem[] = [];
            const known = new Set<string>();
            const add = (item: vscode.CompletionItem): void => {
                const label = typeof item.label === "string" ? item.label : item.label.label;
                if (known.has(label)) return;
                known.add(label);
                items.push(item);
            };

            for (const declaration of context.module?.children || []) add(declarationItem(declaration, "0"));
            for (const declaration of globals(context.indexes)) add(declarationItem(declaration, "1"));

            for (const [name, builtin] of Object.entries(BUILTINS)) {
                const item = new vscode.CompletionItem(name, vscode.CompletionItemKind.Function);
                item.detail = builtin.label;
                item.documentation = new vscode.MarkdownString(builtin.documentation);
                item.insertText = new vscode.SnippetString(`${name}($0)`);
                item.sortText = `2_${name}`;
                add(item);
            }

            for (const type of TYPES) {
                const item = new vscode.CompletionItem(type, vscode.CompletionItemKind.TypeParameter);
                item.detail = builtinTypeDoc(type);
                item.sortText = `3_${type}`;
                add(item);
            }

            for (const keyword of KEYWORDS) {
                const item = new vscode.CompletionItem(keyword, vscode.CompletionItemKind.Keyword);
                item.documentation = new vscode.MarkdownString(KEYWORD_DOCS[keyword]);
                item.sortText = `4_${keyword}`;
                add(item);
            }

            return items;
        }
    }, ".", ":", "<", ","));

    context.subscriptions.push(vscode.languages.registerSignatureHelpProvider(selector, {
        provideSignatureHelp(document, position) {
            const call = findActiveCall(maskNonCode(document.getText()), document.offsetAt(position));
            const builtin = call && BUILTINS[call.name];
            if (!call || !builtin) return undefined;
            const signature = new vscode.SignatureInformation(builtin.label, new vscode.MarkdownString(builtin.documentation));
            signature.parameters = builtin.parameters.map(parameter => new vscode.ParameterInformation(parameter));
            const help = new vscode.SignatureHelp();
            help.signatures = [signature];
            help.activeSignature = 0;
            help.activeParameter = Math.min(call.activeParameter, signature.parameters.length - 1);
            return help;
        }
    }, "(", ","));

    context.subscriptions.push(vscode.languages.registerDocumentLinkProvider(selector, {
        provideDocumentLinks(document) {
            const links: vscode.DocumentLink[] = [];

            for (const include of findIncludes(document.getText())) {
                const target = resolveInclude(include.name, document);
                if (!target) continue;
                const link = new vscode.DocumentLink(new vscode.Range(document.positionAt(include.start), document.positionAt(include.end)), vscode.Uri.file(target));
                link.tooltip = target;
                links.push(link);
            }

            return links;
        }
    }));

    context.subscriptions.push(vscode.languages.registerDocumentSymbolProvider(selector, {
        provideDocumentSymbols(document) {
            const index = indexSource(document.uri, document.getText());

            const toSymbol = (declaration: Declaration): vscode.DocumentSymbol => {
                const range = new vscode.Range(document.positionAt(declaration.start), document.positionAt(Math.max(declaration.end, declaration.nameStart + declaration.name.length)));
                const nameStart = document.positionAt(declaration.nameStart);
                const selection = new vscode.Range(nameStart, nameStart.translate(0, declaration.name.length));
                const detail = declaration.kind === "port" ? (declaration.text.includes("inout") ? "inout" : declaration.input ? "in" : "out") : declaration.kind === "instance" ? declaration.module || "" : declaration.kind;
                const symbol = new vscode.DocumentSymbol(declaration.name, detail, symbolKind(declaration.kind), range.union(selection), selection);
                symbol.children = declaration.children.map(toSymbol);
                return symbol;
            };

            return index.declarations.filter(declaration => !declaration.container).map(toSymbol);
        }
    }));

    function contentsFile(document: vscode.TextDocument): string {
        const directory = path.join(os.tmpdir(), "veles-analyzer");
        fs.mkdirSync(directory, { recursive: true });
        const name = createHash("sha1").update(document.uri.toString()).digest("hex").slice(0, 16);
        const file = path.join(directory, `${name}.vel`);
        fs.writeFileSync(file, document.getText(), "utf8");
        return file;
    }

    function compilerArguments(document: vscode.TextDocument, folder: vscode.WorkspaceFolder | undefined): string[] {
        const args = [document.uri.fsPath];
        if (document.isDirty && contentsSupported) args.push("--contents", contentsFile(document));
        for (const include of includePaths(folder)) args.push(`-I${include}`);
        return args;
    }

    function parseDiagnostics(text: string, document: vscode.TextDocument, cwd: string): vscode.Diagnostic[] {
        const lines = text.replace(ANSI_ESCAPE, "").split(/\r?\n/);
        const result: vscode.Diagnostic[] = [];
        const elsewhere = new Map<string, string[]>();
        let previous: vscode.Diagnostic | undefined;

        for (let i = 0; i < lines.length; i++) {
            const match = DIAGNOSTIC_PATTERN.exec(lines[i]);
            if (!match) continue;
            const file = path.resolve(cwd, match[1]);
            const line = Number(match[2]) - 1;
            const character = Number(match[3]) - 1;
            if (line < 0 || character < 0) continue;

            let length = 1;
            const marker = lines[i + 2]?.match(/^\s*\|\s?(.*)$/)?.[1];
            const carets = marker?.match(/\^+/)?.[0];
            if (carets) length = carets.length;

            const range = new vscode.Range(line, character, line, character + length);
            const message = match[5].trim();

            if (match[4] === "Info") {
                if (previous) {
                    previous.relatedInformation = [...(previous.relatedInformation || []), new vscode.DiagnosticRelatedInformation(new vscode.Location(vscode.Uri.file(file), range), message)];
                }

                continue;
            }

            if (!samePath(file, document.uri.fsPath)) {
                previous = undefined;
                const messages = elsewhere.get(file) || [];
                messages.push(`${path.basename(file)}:${line + 1}:${character + 1}: ${message}`);
                elsewhere.set(file, messages);
                continue;
            }

            if (line >= document.lineCount) continue;
            const severity = match[4] === "Warning" ? vscode.DiagnosticSeverity.Warning : vscode.DiagnosticSeverity.Error;
            const diagnostic = new vscode.Diagnostic(range, message, severity);
            diagnostic.source = "velesc";
            result.push(diagnostic);
            previous = diagnostic;
        }

        if (elsewhere.size) {
            const includes = findIncludes(document.getText());

            for (const [file, messages] of elsewhere) {
                const include = includes.find(candidate => {
                    const target = resolveInclude(candidate.name, document);
                    return target !== undefined && samePath(target, file);
                }) || includes[0];

                const range = include
                    ? new vscode.Range(document.positionAt(include.start), document.positionAt(include.end))
                    : new vscode.Range(0, 0, 0, 0);
                const diagnostic = new vscode.Diagnostic(range, `${path.basename(file)} has ${messages.length} error(s):\n${messages.join("\n")}`, vscode.DiagnosticSeverity.Error);
                diagnostic.source = "velesc";
                result.push(diagnostic);
            }
        }

        return result;
    }

    function checkDocument(document: vscode.TextDocument): void {
        if (document.languageId !== "veles" || document.uri.scheme !== "file") return;
        const uri = document.uri.toString();
        const generation = (generations.get(uri) || 0) + 1;
        generations.set(uri, generation);
        const folder = vscode.workspace.getWorkspaceFolder(document.uri);
        const compiler = findCompiler(folder);

        if (!compiler) {
            diagnostics.delete(document.uri);
            reportCompilerIssue("compiler-not-found", "The Veles compiler (velesc.exe) was not found. Add its folder to PATH or set Veles: Compiler Path.");
            return;
        }

        const cwd = folder?.uri.fsPath || path.dirname(document.uri.fsPath);
        let args: string[];

        try {
            args = ["-fsyntax-only", ...compilerArguments(document, folder)];
        } catch (error) {
            output.appendLine(`Could not write a temporary file: ${String(error)}`);
            return;
        }

        execFile(compiler, args, { cwd, timeout: 15000, maxBuffer: 4 * 1024 * 1024, windowsHide: true }, (error, stdout, stderr) => {
            if (generations.get(uri) !== generation) return;

            if (error && error.killed) {
                reportCompilerIssue("compiler-timeout", "The Veles compiler did not finish within 15 seconds.");
                return;
            }

            if (error && typeof error.code === "string") {
                reportCompilerIssue(`compiler-start-${error.code}`, `Could not start the Veles compiler (error code: ${error.code}). Check Veles: Compiler Path.`);
                return;
            }

            const text = `${stdout || ""}\n${stderr || ""}`;

            if (contentsSupported && text.includes("Unknown option '--contents'")) {
                contentsSupported = false;
                output.appendLine("This velesc does not support --contents; unsaved changes will be checked after saving.");
                checkDocument(document);
                return;
            }

            lastReportedCompilerIssue = undefined;
            diagnostics.set(document.uri, parseDiagnostics(text, document, cwd));
        });
    }

    function scheduleCheck(document: vscode.TextDocument, delay = 400): void {
        const uri = document.uri.toString();
        clearTimeout(timers.get(uri));

        timers.set(uri, setTimeout(() => {
            timers.delete(uri);
            checkDocument(document);
        }, delay));
    }

    context.subscriptions.push(vscode.commands.registerCommand("veles.compileToSystemVerilog", async (resource?: vscode.Uri) => {
        const document = resource ? await vscode.workspace.openTextDocument(resource) : vscode.window.activeTextEditor?.document;

        if (!document || document.languageId !== "veles") {
            void vscode.window.showErrorMessage("Open a Veles file to compile it.");
            return;
        }

        const folder = vscode.workspace.getWorkspaceFolder(document.uri);
        const compiler = findCompiler(folder);

        if (!compiler) {
            void vscode.window.showErrorMessage("The Veles compiler (velesc.exe) was not found. Add its folder to PATH or set Veles: Compiler Path.");
            return;
        }

        const target = document.uri.fsPath.replace(/\.vel$/i, "") + ".sv";
        const cwd = folder?.uri.fsPath || path.dirname(document.uri.fsPath);
        const args = [...compilerArguments(document, folder), "-o", target];

        execFile(compiler, args, { cwd, timeout: 30000, maxBuffer: 4 * 1024 * 1024, windowsHide: true }, async (error, stdout, stderr) => {
            const text = `${stdout || ""}\n${stderr || ""}`;

            if (error) {
                output.clear();
                output.append(text.replace(ANSI_ESCAPE, ""));
                diagnostics.set(document.uri, parseDiagnostics(text, document, cwd));
                void vscode.window.showErrorMessage(`Compiling ${path.basename(document.uri.fsPath)} failed; see the Problems panel.`);
                return;
            }

            const generated = await vscode.workspace.openTextDocument(target);
            await vscode.window.showTextDocument(generated, { viewColumn: vscode.ViewColumn.Beside, preserveFocus: true, preview: true });
        });
    }));

    context.subscriptions.push(
        vscode.workspace.onDidOpenTextDocument(document => checkDocument(document)),
        vscode.workspace.onDidSaveTextDocument(document => {
            if (document.languageId !== "veles") return;
            invalidateIndex();
            scheduleCheck(document, 0);
        }),
        vscode.workspace.onDidChangeTextDocument(event => {
            if (event.document.languageId === "veles" && event.contentChanges.length) scheduleCheck(event.document);
        }),
        vscode.workspace.onDidCloseTextDocument(document => {
            const uri = document.uri.toString();
            clearTimeout(timers.get(uri));
            timers.delete(uri);
            generations.set(uri, (generations.get(uri) || 0) + 1);
            diagnostics.delete(document.uri);
        }),
        vscode.workspace.onDidChangeConfiguration(event => {
            if (event.affectsConfiguration("veles")) {
                invalidateIndex();
                contentsSupported = true;
                for (const document of vscode.workspace.textDocuments) checkDocument(document);
            }
        }),
        vscode.workspace.onDidChangeWorkspaceFolders(invalidateIndex)
    );

    const watcher = vscode.workspace.createFileSystemWatcher("**/*.vel");
    context.subscriptions.push(
        watcher,
        watcher.onDidCreate(invalidateIndex),
        watcher.onDidChange(invalidateIndex),
        watcher.onDidDelete(invalidateIndex)
    );

    void getWorkspaceIndex();
    for (const document of vscode.workspace.textDocuments) checkDocument(document);
}

export function deactivate(): void {}
