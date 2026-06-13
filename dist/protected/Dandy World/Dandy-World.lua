-- ===== Key System (must pass before the script runs) =====
local function __y2k_keygate()
-- ============================================================================
--  Y2k key provider  (drop-in replacement for the Junkie SDK)
--  Talks to YOUR Cloudflare Worker + KV key server (server-side hashing, HWID
--  auto-bind, expiry). CONFIGURE the two URLs below. Server: server-example/.
-- ============================================================================
local Junkie = {}
do
	local KEY_API  = "https://y2k-keys.y2kscript.workers.dev"  -- your deployed Worker (LIVE)
	local KEY_LINK = "https://work.ink/2Dgt/ks-int12887-kq76mlra7lo" -- work.ink key link

	local HttpService = game:GetService("HttpService")
	local function enc(s) local ok, r = pcall(function() return HttpService:UrlEncode(s) end) return ok and r or s end
	local function httpGet(u)
		for _, f in ipairs({
			function() return game:HttpGetAsync(u) end,
			function() return game:HttpGet(u) end,
			function() return request and request({ Url = u, Method = "GET" }).Body end,
		}) do
			local ok, b = pcall(f); if ok and type(b) == "string" then return b end
		end
		return nil
	end
	local function hwid()
		local id
		pcall(function() id = (gethwid and gethwid()) or (get_hwid and get_hwid()) end)
		if not id then pcall(function() id = game:GetService("RbxAnalyticsService"):GetClientId() end) end
		return tostring(id or "unknown")
	end

	function Junkie.get_key_link() return KEY_LINK end
	function Junkie.check_key(key)
		if not key or key == "" then return { valid = false, message = "No key entered" } end
		local hw = hwid()
		local url = KEY_API .. "/check?key=" .. enc(key) .. "&hwid=" .. enc(hw) .. "&t=" .. tostring(os.time())
		local body = httpGet(url)
		if not body then return { valid = false, message = "Key server unreachable" } end
		local b = string.lower(body)
		if string.find(b, "ok", 1, true) then
			getgenv().HWID = hw
			return { valid = true, message = "KEY_VALID", hwid = hw }
		elseif string.find(b, "expired", 1, true) then
			return { valid = false, message = "Key expired" }
		elseif string.find(b, "hwid", 1, true) then
			return { valid = false, message = "Key locked to another device" }
		else
			return { valid = false, message = "Invalid key" }
		end
	end
end


local TweenService = game:GetService("TweenService")
local UserInputService = game:GetService("UserInputService")
local RunService = game:GetService("RunService")
local Players = game:GetService("Players")
local Lighting = game:GetService("Lighting")
local HttpService = game:GetService("HttpService")

local Icons = {
	Shield = "rbxassetid://105619007041452",
	Loading = "rbxassetid://116535712789945",
	Lock = "rbxassetid://114355063515473",
	Key = "rbxassetid://93569468678423",
	Check = "rbxassetid://119783053916823",
	CheckCircle = "rbxassetid://10709790644",
	XCircle = "rbxassetid://10747384394",
	Warning = "rbxassetid://130226573962640",
	Globe = "rbxassetid://10734950309",
	Info = "rbxassetid://94529541997278",
	ExternalLink = "rbxassetid://71038734318580",
	Copy = "rbxassetid://107485544510830",
	Spinner = "rbxassetid://10709767827",
	Database = "rbxassetid://114209748010261",
	Sparkles = "rbxassetid://10709767827",
	ErrorFolder = "rbxassetid://113312905787220",
	Candy = "rbxassetid://10709767827",
	JunkieNewIcon = "rbxassetid://75038032192167"
}

local function hasFileSystemSupport()
    local hasWritefile = pcall(function() return type(writefile) == "function" end)
    local hasReadfile = pcall(function() return type(readfile) == "function" end)
    local hasIsfile = pcall(function() return type(isfile) == "function" end)
    return hasWritefile and hasReadfile and hasIsfile
end

local fileSystemSupported = hasFileSystemSupport()

local function saveVerifiedKey(key)
    if not fileSystemSupported then return false end
    local ok = pcall(function()
        writefile("verified_key.txt", key)
    end)
    return ok
end

local function loadVerifiedKey()
    if not fileSystemSupported then 
        return nil 
    end
    
    local ok, content = pcall(function()
        return readfile("verified_key.txt")
    end)
    
    if not ok or not content then 
        return nil 
    end
    return content
end

local function clearSavedKey()
    if not fileSystemSupported then return false end
    local ok = pcall(function() delfile("verified_key.txt") end)
    return ok
end

local Configuration = {
	ScreenGuiName = "JunkieKeySystem",
	Window = {Size = UDim2.new(0, 333, 0, 500)},
	Colors = {
		Bg = Color3.fromRGB(12, 12, 12),
		Primary = Color3.fromRGB(59, 130, 246),
		PrimaryDark = Color3.fromRGB(37, 99, 235),
		StatusIdle = Color3.fromRGB(249, 115, 22),
		StatusSuccess = Color3.fromRGB(16, 185, 129),
		StatusError = Color3.fromRGB(239, 68, 68),
		StatusVerifying = Color3.fromRGB(59, 130, 246),
		StatusWarning = Color3.fromRGB(254, 188, 46),
		TextMain = Color3.fromRGB(255, 255, 255),
		TextSec = Color3.fromRGB(161, 161, 170),
		TextMuted = Color3.fromRGB(113, 113, 122),
		Border = Color3.fromRGB(255, 255, 255),
		TrafficRed = Color3.fromRGB(255, 95, 87),
		TrafficYellow = Color3.fromRGB(254, 188, 46),
		TrafficGreen = Color3.fromRGB(40, 200, 64),
		Success = Color3.fromRGB(50, 205, 110),
		Error = Color3.fromRGB(245, 70, 90),
		Warning = Color3.fromRGB(255, 200, 50)
	},
	BorderTransparency = 0.15,
	Animations = {
		VeryFast = 0.1,
		Fast = 0.2,
		Medium = 0.4,
		Slow = 0.5,
		VerySlow = 0.6,
		Bounce = 0.6
	},
	Fonts = {
		Title = 24,
		Subtitle = 12,
		Button = 14,
		Input = 16,
		Body = 13,
		Small = 11,
		Tiny = 12
	}
}

local Utils = {}

Utils.Tween = function(obj, props, time, style, dir)
	local t =
		TweenService:Create(
		obj,
		TweenInfo.new(time or 0.3, style or Enum.EasingStyle.Quint, dir or Enum.EasingDirection.Out),
		props
	)
	t:Play()
	return t
end

Utils.CreateCorner = function(parent, radius)
	local corner = Instance.new("UICorner")
	corner.CornerRadius = UDim.new(0, radius or Configuration.CornerRadius)
	corner.Parent = parent
	return corner
end

Utils.Round = function(obj, radius)
	local c = Instance.new("UICorner")
	c.CornerRadius = UDim.new(0, radius or 12)
	c.Parent = obj
	return c
end

Utils.TweenBack = function(instance, properties, duration)
	return Utils.Tween(instance, properties, duration, Enum.EasingStyle.Back, Enum.EasingDirection.Out)
end

Utils.CreateStroke = function(parent, color, thickness, transparency)
	local stroke = Instance.new("UIStroke")
	stroke.Color = color or Configuration.Colors.Border
	stroke.Thickness = thickness or 1
	stroke.Transparency = transparency or 0.77
	stroke.ApplyStrokeMode = Enum.ApplyStrokeMode.Border
	stroke.Parent = parent
	return stroke
end

Utils.Stroke = function(obj, color, thick, trans)
	local s = Instance.new("UIStroke")
	s.Color = color or Color3.new(1, 1, 1)
	s.Thickness = thick or 1
	s.Transparency = trans or 0.9
	s.ApplyStrokeMode = Enum.ApplyStrokeMode.Border
	s.Parent = obj
	return s
end

Utils.CreateGradient = function(parent, color1, color2, rotation)
	local gradient = Instance.new("UIGradient")
	gradient.Color =
		ColorSequence.new(
		{
			ColorSequenceKeypoint.new(0, color1),
			ColorSequenceKeypoint.new(1, color2)
		}
	)
	gradient.Rotation = rotation or 300
	gradient.Parent = parent
	return gradient
end

local function SetBlur(enabled)
	local blur = Lighting:FindFirstChild("JunkieBlur")
	if enabled then
		if not blur then
			blur = Instance.new("BlurEffect")
			blur.Name = "JunkieBlur"
			blur.Size = 0
			blur.Parent = Lighting
		end
		Utils.Tween(blur, {Size = 24}, Configuration.Animations.Bounce)
	elseif blur then
		Utils.Tween(blur, {Size = 0}, Configuration.Animations.Medium)
		task.delay(
			0.4,
			function()
				blur:Destroy()
			end
		)
	end
end

local ToastSystem = {ActiveToasts = {}, MaxToasts = 3, ToastSpacing = 10}

ToastSystem.Create = function(parent, message, toastType, duration, statusCode)
	local colors = {
		success = Configuration.Colors.Success,
		error = Configuration.Colors.Error,
		warning = Configuration.Colors.Warning,
		info = Configuration.Colors.Primary
	}
	local icons = {
		success = Icons.CheckCircle,
		error = Icons.ErrorFolder,
		warning = Icons.Warning,
		info = Icons.Info
	}
	local toastColor = colors[toastType] or colors.Bg
	local toastIcon = icons[toastType] or nil
	if #ToastSystem.ActiveToasts >= ToastSystem.MaxToasts then
		local oldest = table.remove(ToastSystem.ActiveToasts, 1)
		if oldest and oldest.Parent then
			oldest:Destroy()
		end
	end
	local toastHeight = 56
	local toast = Instance.new("Frame")
	toast.Name = tick()
	toast.Size = UDim2.new(0, 0, 0, toastHeight)
	toast.Position = UDim2.new(0.5, 0, 0, 20)
	toast.AnchorPoint = Vector2.new(0.5, 0)
	toast.BackgroundColor3 = Configuration.Colors.Bg
	toast.BackgroundTransparency = 0.5
	toast.BorderSizePixel = 0
	toast.ZIndex = 300
	toast.ClipsDescendants = true
	toast.Parent = parent
	Utils.Round(toast, 14)
	Utils.CreateStroke(toast, toastColor, 1, 0.1)
	Utils.CreateGradient(toast, Configuration.Colors.Bg, Configuration.Colors.Bg, 1)
	local iconBg = Instance.new("Frame")
	iconBg.Name = "IconBg"
	iconBg.Size = UDim2.new(0, 36, 0, 36)
	iconBg.Position = UDim2.new(0, 12, 0.5, 0)
	iconBg.AnchorPoint = Vector2.new(0, 0.5)
	iconBg.BackgroundColor3 = toastColor
	iconBg.BackgroundTransparency = 0.85
	iconBg.BorderSizePixel = 0
	iconBg.ZIndex = 301
	iconBg.Parent = toast
	Utils.Round(iconBg, 18)
	local icon = Instance.new("ImageLabel")
	icon.Name = "Icon"
	icon.Size = UDim2.new(0, 20, 0, 20)
	icon.Position = UDim2.new(0.5, 0, 0.5, 0)
	icon.AnchorPoint = Vector2.new(0.5, 0.5)
	icon.BackgroundTransparency = 1
	icon.Image = toastIcon
	icon.ImageColor3 = toastColor
	icon.ZIndex = 302
	icon.Parent = iconBg
	local textContainer = Instance.new("Frame")
	textContainer.Name = "TextContainer"
	textContainer.Size = UDim2.new(1, statusCode and -110 or -60, 1, 0)
	textContainer.Position = UDim2.new(0, 56, 0, 0)
	textContainer.BackgroundTransparency = 1
	textContainer.ZIndex = 301
	textContainer.Parent = toast
	local text = Instance.new("TextLabel")
	text.Name = "Message"
	text.Size = UDim2.new(1, 0, 1, 0)
	text.BackgroundTransparency = 1
	text.Text = message or ""
	text.TextColor3 = Configuration.Colors.TextMain
	text.TextSize = Configuration.Fonts.Body
	text.Font = Enum.Font.GothamMedium
	text.TextXAlignment = Enum.TextXAlignment.Left
	text.TextYAlignment = Enum.TextYAlignment.Center
	text.TextWrapped = true
	text.ZIndex = 301
	text.Parent = textContainer
	if statusCode then
		local statusBadge = Instance.new("Frame")
		statusBadge.Name = "StatusBadge"
		statusBadge.Size = UDim2.new(0, 44, 0, 28)
		statusBadge.Position = UDim2.new(1, -12, 0.5, 0)
		statusBadge.AnchorPoint = Vector2.new(1, 0.5)
		statusBadge.BackgroundColor3 = toastColor
		statusBadge.BackgroundTransparency = 0.8
		statusBadge.BorderSizePixel = 0
		statusBadge.ZIndex = 301
		statusBadge.Parent = toast
		Utils.Round(statusBadge, 8)
		Utils.CreateStroke(statusBadge, toastColor, 1, Configuration.BorderTransparency)
		local statusCodeLabel = Instance.new("TextLabel")
		statusCodeLabel.Name = "StatusCode"
		statusCodeLabel.Size = UDim2.new(1, 0, 1, 0)
		statusCodeLabel.BackgroundTransparency = 1
		statusCodeLabel.Text = tostring(statusCode)
		statusCodeLabel.TextColor3 = toastColor
		statusCodeLabel.TextSize = Configuration.Fonts.Small
		statusCodeLabel.Font = Enum.Font.GothamBold
		statusCodeLabel.ZIndex = 302
		statusCodeLabel.Parent = statusBadge
	end
	table.insert(ToastSystem.ActiveToasts, toast)
	ToastSystem.RepositionToasts()
	local targetWidth = 320
	Utils.TweenBack(toast, {Size = UDim2.new(0, targetWidth, 0, toastHeight)}, Configuration.Animations.Medium)
	task.delay(
		duration or 3.5,
		function()
			if toast.Parent then
				Utils.Tween(
					toast,
					{
						Position = UDim2.new(0.5, 0, 0, -80),
						BackgroundTransparency = 1
					},
					Configuration.Animations.Medium
				)
				for i, t in ipairs(ToastSystem.ActiveToasts) do
					if t == toast then
						table.remove(ToastSystem.ActiveToasts, i)
						break
					end
				end
				task.wait(Configuration.Animations.Medium)
				toast:Destroy()
				ToastSystem.RepositionToasts()
			end
		end
	)
	return toast
end

ToastSystem.RepositionToasts = function()
	for i, toast in ipairs(ToastSystem.ActiveToasts) do
		local targetY = 20 + ((i - 1) * (60 + ToastSystem.ToastSpacing))
		Utils.Tween(toast, {Position = UDim2.new(0.5, 0, 0, targetY)}, Configuration.Animations.Medium)
	end
end

local function Build()
	local parent = game:GetService("CoreGui")
	local old = parent:FindFirstChild(Configuration.ScreenGuiName)
	if old then
		old:Destroy()
	end
	local screen = Instance.new("ScreenGui")
	screen.Name = Configuration.ScreenGuiName
	screen.ResetOnSpawn = false
	screen.Parent = parent

	-- Discord banner (top of screen, transparent, blinking + glow)
	local discordBanner = Instance.new("TextLabel")
	discordBanner.Name = "DiscordBanner"
	discordBanner.Size = UDim2.new(0, 400, 0, 32)
	discordBanner.Position = UDim2.new(0.5, 0, 0, 10)
	discordBanner.AnchorPoint = Vector2.new(0.5, 0)
	discordBanner.BackgroundTransparency = 1
	discordBanner.Text = "Join https://discord.gg/EFFKrfFkPQ"
	discordBanner.TextColor3 = Color3.fromRGB(88, 101, 242)
	discordBanner.TextSize = 16
	discordBanner.Font = Enum.Font.GothamBold
	discordBanner.TextTransparency = 0
	discordBanner.Parent = screen

	local bannerStroke = Instance.new("UIStroke")
	bannerStroke.Color = Color3.fromRGB(88, 101, 242)
	bannerStroke.Thickness = 2
	bannerStroke.Transparency = 0.3
	bannerStroke.Parent = discordBanner

	task.spawn(function()
		while discordBanner and discordBanner.Parent do
			Utils.Tween(discordBanner, {TextTransparency = 0.4}, 0.6)
			Utils.Tween(bannerStroke, {Transparency = 0.7}, 0.6)
			task.wait(0.6)
			Utils.Tween(discordBanner, {TextTransparency = 0}, 0.6)
			Utils.Tween(bannerStroke, {Transparency = 0.3}, 0.6)
			task.wait(0.6)
		end
	end)

	local overlay = Instance.new("Frame")
	overlay.Size = UDim2.fromScale(1, 1)
	overlay.BackgroundColor3 = Color3.new(0, 0, 0)
	overlay.BackgroundTransparency = 1
	overlay.Parent = screen
	Utils.Tween(overlay, {BackgroundTransparency = 1}, 1)
	SetBlur(true)
	local main = Instance.new("Frame")
	main.Size = Configuration.Window.Size
	main.Position = UDim2.new(0.5, 0, 0.5, 60)
	main.AnchorPoint = Vector2.new(0.5, 0.5)
	main.BackgroundColor3 = Configuration.Colors.Bg
	main.BackgroundTransparency = 0.2
	main.ClipsDescendants = true
	main.Parent = screen
	Utils.Round(main, 24)
	Utils.Stroke(main, Color3.new(1, 1, 1), 1, 0.92)
	local glass = Instance.new("Frame")
	glass.Size = UDim2.fromScale(1, 1)
	glass.BackgroundColor3 = Color3.new(1, 1, 1)
	glass.BackgroundTransparency = 0.985
	glass.ZIndex = 0
	glass.Parent = main
	Utils.Round(glass, 24)
	local bar = Instance.new("Frame")
	bar.Size = UDim2.new(1, 0, 0, 54)
	bar.BackgroundTransparency = 1
	bar.Parent = main
	local dots = Instance.new("Frame")
	dots.Size = UDim2.new(0, 54, 0, 12)
	dots.Position = UDim2.new(0, 20, 0.5, 0)
	dots.AnchorPoint = Vector2.new(0, 0.5)
	dots.BackgroundTransparency = 1
	dots.Parent = bar
	local dColors = {
		Configuration.Colors.TrafficRed,
		Configuration.Colors.TrafficYellow,
		Configuration.Colors.TrafficGreen
	}
	for i, c in ipairs(dColors) do
		local d = Instance.new("Frame")
		d.Size = UDim2.fromOffset(12, 12)
		d.Position = UDim2.fromOffset((i - 1) * 18, 0)
		d.BackgroundColor3 = c
		d.BorderSizePixel = 0
		d.Parent = dots
		Utils.Round(d, 6)
	end
	local titleText = Instance.new("TextLabel")
	titleText.Size = UDim2.new(1, 0, 1, 0)
	titleText.Text = "JUNKIE"
	titleText.TextColor3 = Color3.new(1, 1, 1)
	titleText.TextTransparency = 0.7
	titleText.TextSize = 10
	titleText.Font = Enum.Font.GothamBold
	titleText.BackgroundTransparency = 1
	titleText.Parent = bar
	local content = Instance.new("ScrollingFrame")
	content.Size = UDim2.new(1, 0, 1, -54)
	content.Position = UDim2.new(0, 0, 0, 54)
	content.BackgroundTransparency = 1
	content.ScrollBarThickness = 0
	content.CanvasSize = UDim2.new(0, 0, 0, 440)
	content.Parent = main
	local list = Instance.new("UIListLayout")
	list.Padding = UDim.new(0, 24)
	list.HorizontalAlignment = Enum.HorizontalAlignment.Center
	list.Parent = content
	local pad = Instance.new("UIPadding")
	pad.PaddingTop = UDim.new(0, 5)
	pad.Parent = content
	local logoContainer = Instance.new("Frame")
	logoContainer.Size = UDim2.fromOffset(80, 80)
	logoContainer.BackgroundColor3 = Configuration.Colors.Primary
	logoContainer.Parent = content
	Utils.Round(logoContainer, 20)
	local grad = Instance.new("UIGradient")
	grad.Color = ColorSequence.new(Configuration.Colors.Primary, Configuration.Colors.PrimaryDark)
	grad.Rotation = 45
	grad.Parent = logoContainer
	local sIcon = Instance.new("ImageLabel")
	sIcon.Size = UDim2.fromScale(1, 1)
	sIcon.Position = UDim2.fromScale(0.5, 0.5)
	sIcon.AnchorPoint = Vector2.new(0.5, 0.5)
	sIcon.Image = Icons.JunkieNewIcon
	sIcon.ScaleType = Enum.ScaleType.Fit
	sIcon.BackgroundTransparency = 1
	sIcon.Parent = logoContainer
	local titleArea = Instance.new("Frame")
	titleArea.Size = UDim2.new(1, 0, 0, 44)
	titleArea.BackgroundTransparency = 1
	titleArea.Parent = content
	local mainTitle = Instance.new("TextLabel")
	mainTitle.Size = UDim2.new(1, 0, 0, 26)
	mainTitle.Text = "Junkie"
	mainTitle.TextColor3 = Color3.new(1, 1, 1)
	mainTitle.TextSize = 26
	mainTitle.Font = Enum.Font.GothamBold
	mainTitle.BackgroundTransparency = 1
	mainTitle.Parent = titleArea
	local subTitle = Instance.new("TextLabel")
	subTitle.Size = UDim2.new(1, 0, 0, 16)
	subTitle.Position = UDim2.fromOffset(0, 28)
	subTitle.Text = "junkie-development.de"
	subTitle.TextColor3 = Configuration.Colors.TextSec
	subTitle.TextSize = 13
	subTitle.Font = Enum.Font.Gotham
	subTitle.BackgroundTransparency = 1
	subTitle.Parent = titleArea
	local statusCard = Instance.new("Frame")
	statusCard.Size = UDim2.new(0, 280, 0, 68)
	statusCard.BackgroundColor3 = Color3.new(1, 1, 1)
	statusCard.BackgroundTransparency = 0.96
	statusCard.Parent = content
	Utils.Round(statusCard, 16)
	local sStroke = Utils.Stroke(statusCard, Color3.new(1, 1, 1), 1, 0.95)
	local sIconBg = Instance.new("Frame")
	sIconBg.Size = UDim2.fromOffset(42, 42)
	sIconBg.Position = UDim2.new(0, 14, 0.5, 0)
	sIconBg.AnchorPoint = Vector2.new(0, 0.5)
	sIconBg.BackgroundColor3 = Configuration.Colors.StatusIdle
	sIconBg.BackgroundTransparency = 0.9
	sIconBg.Parent = statusCard
	Utils.Round(sIconBg, 21)
	local sImg = Instance.new("ImageLabel")
	sImg.Size = UDim2.fromScale(0.5, 0.5)
	sImg.Position = UDim2.fromScale(0.5, 0.5)
	sImg.AnchorPoint = Vector2.new(0.5, 0.5)
	sImg.Image = Icons.Lock
	sImg.ImageColor3 = Configuration.Colors.StatusIdle
	sImg.BackgroundTransparency = 1
	sImg.Parent = sIconBg
	local sLabel = Instance.new("TextLabel")
	sLabel.Size = UDim2.new(1, -70, 0, 14)
	sLabel.Position = UDim2.fromOffset(70, 16)
	sLabel.Text = "CURRENT STATUS"
	sLabel.TextColor3 = Configuration.Colors.TextMuted
	sLabel.TextSize = 10
	sLabel.Font = Enum.Font.GothamBold
	sLabel.TextXAlignment = Enum.TextXAlignment.Left
	sLabel.BackgroundTransparency = 1
	sLabel.Parent = statusCard
	local sValue = Instance.new("TextLabel")
	sValue.Size = UDim2.new(1, -70, 0, 20)
	sValue.Position = UDim2.fromOffset(70, 32)
	sValue.Text = "No key detected"
	sValue.TextColor3 = Configuration.Colors.StatusIdle
	sValue.TextSize = 15
	sValue.Font = Enum.Font.GothamMedium
	sValue.TextXAlignment = Enum.TextXAlignment.Left
	sValue.BackgroundTransparency = 1
	sValue.Parent = statusCard
	local inputFrame = Instance.new("Frame")
	inputFrame.Size = UDim2.new(0, 280, 0, 52)
	inputFrame.BackgroundColor3 = Color3.new(1, 1, 1)
	inputFrame.BackgroundTransparency = 0.975
	inputFrame.Parent = content
	Utils.Round(inputFrame, 14)
	local iStroke = Utils.Stroke(inputFrame, Color3.new(1, 1, 1), 1, 0.95)
	local kIcon = Instance.new("ImageLabel")
	kIcon.Size = UDim2.fromOffset(18, 18)
	kIcon.Position = UDim2.new(0, 14, 0.5, 0)
	kIcon.AnchorPoint = Vector2.new(0, 0.5)
	kIcon.Image = Icons.Key
	kIcon.ImageColor3 = Configuration.Colors.TextMuted
	kIcon.BackgroundTransparency = 1
	kIcon.Parent = inputFrame
	local box = Instance.new("TextBox")
	box.Size = UDim2.new(1, -85, 1, 0)
	box.Position = UDim2.fromOffset(45, 0)
	box.Text = ""
	box.PlaceholderText = "Enter your key..."
	box.TextColor3 = Color3.new(1, 1, 1)
	box.TextSize = 14
	box.Font = Enum.Font.Gotham
	box.BackgroundTransparency = 1
	box.TextXAlignment = Enum.TextXAlignment.Left
	box.Parent = inputFrame
	local paste = Instance.new("ImageButton")
	paste.Size = UDim2.fromOffset(18, 18)
	paste.Position = UDim2.new(1, -14, 0.5, 0)
	paste.AnchorPoint = Vector2.new(1, 0.5)
	paste.Image = Icons.Copy
	paste.ImageColor3 = Configuration.Colors.TextMuted
	paste.BackgroundTransparency = 1
	paste.Parent = inputFrame
	local btnRow = Instance.new("Frame")
	btnRow.Size = UDim2.new(0, 280, 0, 50)
	btnRow.BackgroundTransparency = 1
	btnRow.Parent = content
	local redeem = Instance.new("TextButton")
	redeem.Size = UDim2.new(0.5, -8, 1, 0)
	redeem.BackgroundColor3 = Configuration.Colors.Primary
	redeem.Text = "Redeem"
	redeem.TextColor3 = Color3.new(1, 1, 1)
	redeem.Font = Enum.Font.GothamBold
	redeem.TextSize = 14
	redeem.AutoButtonColor = false
	redeem.Parent = btnRow
	Utils.Round(redeem, 14)
	local getKey = Instance.new("TextButton")
	getKey.Size = UDim2.new(0.5, -8, 1, 0)
	getKey.Position = UDim2.new(0.5, 8, 0, 0)
	getKey.BackgroundColor3 = Color3.new(1, 1, 1)
	getKey.BackgroundTransparency = 0.955
	getKey.Text = "Get Key"
	getKey.TextColor3 = Color3.new(1, 1, 1)
	getKey.Font = Enum.Font.GothamBold
	getKey.TextSize = 14
	getKey.AutoButtonColor = false
	getKey.Parent = btnRow
	Utils.Round(getKey, 14)
	Utils.Stroke(getKey, Color3.new(1, 1, 1), 1, 0.94)
	local function ApplyHover(btn)
		local baseColor = btn.BackgroundColor3
		btn.MouseEnter:Connect(
			function()
				Utils.Tween(
					btn,
					{
						BackgroundColor3 = baseColor:Lerp(Color3.new(1, 1, 1), 0.1)
					},
					0.2
				)
				Utils.Tween(
					btn,
					{
						Size = UDim2.new(btn.Size.X.Scale, btn.Size.X.Offset + 4, btn.Size.Y.Scale, btn.Size.Y.Offset + 2)
					},
					0.2
				)
			end
		)
		btn.MouseLeave:Connect(
			function()
				Utils.Tween(btn, {BackgroundColor3 = baseColor}, 0.2)
				Utils.Tween(
					btn,
					{
						Size = UDim2.new(btn.Size.X.Scale, btn.Size.X.Offset - 4, btn.Size.Y.Scale, btn.Size.Y.Offset - 2)
					},
					0.2
				)
			end
		)
	end
	ApplyHover(redeem)
	ApplyHover(getKey)
	box.Focused:Connect(
		function()
			Utils.Tween(iStroke, {Transparency = 0.5, Thickness = 1.2}, 0.3)
		end
	)
	box.FocusLost:Connect(
		function()
			Utils.Tween(iStroke, {Transparency = 0.95, Thickness = 1}, 0.3)
		end
	)
	local spinConnection
	local dotsThread
	local function SetStatus(state)
		if spinConnection then
			spinConnection:Disconnect()
			spinConnection = nil
			sImg.Rotation = 0
		end
		if dotsThread then
			task.cancel(dotsThread)
			dotsThread = nil
		end
		local color = Configuration.Colors.StatusIdle
		local icon = Icons.Lock
		local text = "No key detected"
		if state == "verifying" then
			color = Configuration.Colors.StatusVerifying
			icon = Icons.Loading
			text = "Verifying access"
			spinConnection =
				RunService.Heartbeat:Connect(
				function(dt)
					if not sImg or not sImg.Parent then
						if spinConnection then
							spinConnection:Disconnect()
						end
						spinConnection = nil
						return
					end
					sImg.Rotation = (sImg.Rotation + dt * 360) % 360
				end
			)
			local dots = {".", "..", "...", ""}
			local i = 1
			dotsThread =
				task.spawn(
				function()
					while sValue and sValue.Parent do
						if not sValue.Text:find("Verifying access", 1, true) then
							break
						end
						sValue.Text = text .. dots[i]
						i = (i % #dots) + 1
						task.wait(0.45)
					end
				end
			)
		elseif state == "success" then
			color = Configuration.Colors.StatusSuccess
			icon = Icons.CheckCircle
			text = "Access Granted"
		elseif state == "error" then
			color = Configuration.Colors.StatusError
			icon = Icons.XCircle
			text = "Invalid Key"
		end
		Utils.Tween(sValue, {TextColor3 = color}, 0.35)
		Utils.Tween(sImg, {ImageColor3 = color}, 0.35)
		Utils.Tween(sIconBg, {BackgroundColor3 = color}, 0.35)
		sValue.Text = text
		sImg.Image = icon
	end
	redeem.MouseButton1Click:Connect(
		function()
			local key = box.Text:upper()
			SetStatus("verifying")
			redeem.Text = "..."
			redeem.Active = false
            local result = Junkie.check_key(key)
			redeem.Active = true
			redeem.Text = "Redeem"
			if not result then
				SetStatus("error")
				ToastSystem.Create(screen, "API request failed: " .. tostring(result), "error")
				return
			end
			if result.valid then
                saveVerifiedKey(key)
                getgenv().SCRIPT_KEY = key
                SetStatus("success")
                ToastSystem.Create(screen, "Access granted!", "success", nil, status)
                task.wait(0.8)
                SetBlur(false)
                Utils.Tween(
                    main,
                    {
                        Position = UDim2.new(0.5, 0, 0.5, 100),
                        BackgroundTransparency = 1
                    },
                    0.7,
                    Enum.EasingStyle.Exponential,
                    Enum.EasingDirection.In
                )
                task.delay(
                    0.7,
                    function()
                        screen:Destroy()
                    end
                )
			else
				SetStatus("error")
				ToastSystem.Create(screen, result.message or "Invalid key", "error", nil, status)
			end
		end
	)
	getKey.MouseButton1Click:Connect(
		function()
			setclipboard(Junkie.get_key_link())
			ToastSystem.Create(screen, "Key link has been copied to clipboard", "success")
		end
	)
	paste.MouseButton1Click:Connect(
		function()
			ToastSystem.Create(screen, "Paste functionality not supported in Roblox (security reasons)", "warning")
		end
	)
	main.Position = UDim2.new(0.5, 0, 0.5, 100)
	main.BackgroundTransparency = 1
	Utils.Tween(
		main,
		{
			Position = UDim2.new(0.5, 0, 0.5, 0),
			BackgroundTransparency = 0.2
		},
		1,
		Enum.EasingStyle.Exponential
	)
	local dragging, dragStart, startPos
	bar.InputBegan:Connect(
		function(input)
			if input.UserInputType == Enum.UserInputType.MouseButton1 then
				dragging = true
				dragStart = input.Position
				startPos = main.Position
			end
		end
	)
	UserInputService.InputChanged:Connect(
		function(input)
			if dragging and input.UserInputType == Enum.UserInputType.MouseMovement then
				local delta = input.Position - dragStart
				main.Position =
					UDim2.new(startPos.X.Scale, startPos.X.Offset + delta.X, startPos.Y.Scale, startPos.Y.Offset + delta.Y)
			end
		end
	)
	UserInputService.InputEnded:Connect(
		function(input)
			if input.UserInputType == Enum.UserInputType.MouseButton1 then
				dragging = false
			end
		end
	)
	return screen
end

local savedKey = loadVerifiedKey()
local keyToCheck = savedKey
if not keyToCheck then
    keyToCheck = getgenv().SCRIPT_KEY
end

local result = Junkie.check_key(keyToCheck)
if result and result.valid then
    if result.message == "KEYLESS" then
        getgenv().SCRIPT_KEY = "KEYLESS"
    elseif result.message == "KEY_VALID" then
        if not savedKey and keyToCheck then
            saveVerifiedKey(keyToCheck)
        end
        getgenv().SCRIPT_KEY = keyToCheck
    else
        Build()
    end
else
    Build()
end

while not getgenv().SCRIPT_KEY do
    task.wait(0.1)
end
end
__y2k_keygate()
-- ===== Protected payload =====
-- Protected with Vm runtime. Tampering halts execution.
-- Vm protection runtime (bundled). Do not edit by hand.
local Crypt = (function()
--!nonstrict
-- ============================================================================
--  Crypt.lua  --  lightweight obfuscation / integrity primitives
--  Part of the Vm protection runtime. No external deps. Luau-safe.
--
--  Provides: XOR string cipher, FNV-1a hash, base64, and a small PRNG so the
--  runtime can hide embedded strings (URLs, function names) and verify
--  integrity without leaving plaintext secrets in the bytecode.
-- ============================================================================

local Crypt = {}

local schar, sbyte, ssub, srep = string.char, string.byte, string.sub, string.rep
local tconcat = table.concat
local bxor = bit32 and bit32.bxor or function(a, b)
	local r, p = 0, 1
	while a > 0 or b > 0 do
		local x, y = a % 2, b % 2
		if x ~= y then r = r + p end
		a, b, p = (a - x) / 2, (b - y) / 2, p * 2
	end
	return r
end

-- 32-bit multiply mod 2^32 that stays within double precision (2^53).
-- Splitting the accumulator into hi/lo 16-bit halves keeps every intermediate
-- product under 2^42, so no precision is lost (a plain h*16777619 overflows 2^53).
local function mul32(a, b)
	local ah = (a - a % 65536) / 65536   -- floor(a / 2^16), < 2^16
	local al = a % 65536                  -- a mod 2^16, < 2^16
	return ((ah * b % 65536) * 65536 + al * b) % 4294967296
end

-- FNV-1a 32-bit hash of a string (used for integrity fingerprints)
function Crypt.hash(s)
	local h = 2166136261
	for i = 1, #s do
		h = bxor(h, sbyte(s, i))
		h = mul32(h, 16777619)
	end
	return h
end

-- repeating-key XOR cipher (symmetric). key is a string.
function Crypt.xor(data, key)
	local out, kl = {}, #key
	for i = 1, #data do
		out[i] = schar(bxor(sbyte(data, i), sbyte(key, (i - 1) % kl + 1)))
	end
	return tconcat(out)
end

-- deterministic PRNG (xorshift) seeded from a string; for shuffling/jitter
function Crypt.rng(seed)
	local state = (type(seed) == "string") and Crypt.hash(seed) or (seed or 0x1234567)
	if state == 0 then state = 0x9E3779B9 end
	return function()
		state = bxor(state, (state * 32) % 4294967296)
		state = bxor(state, math.floor(state / 8))
		state = bxor(state, (state * 16384) % 4294967296)
		state = state % 4294967296
		return state / 4294967296
	end
end

-- base64 (so ciphertext survives as a string literal in the bundle)
local B64 = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/"
function Crypt.b64encode(data)
	local out = {}
	for i = 1, #data, 3 do
		local a, b, c = sbyte(data, i), sbyte(data, i + 1), sbyte(data, i + 2)
		local n = a * 65536 + (b or 0) * 256 + (c or 0)
		local c1 = math.floor(n / 262144) % 64
		local c2 = math.floor(n / 4096) % 64
		local c3 = math.floor(n / 64) % 64
		local c4 = n % 64
		out[#out + 1] = ssub(B64, c1 + 1, c1 + 1)
		out[#out + 1] = ssub(B64, c2 + 1, c2 + 1)
		out[#out + 1] = b and ssub(B64, c3 + 1, c3 + 1) or "="
		out[#out + 1] = c and ssub(B64, c4 + 1, c4 + 1) or "="
	end
	return tconcat(out)
end

local B64I
function Crypt.b64decode(data)
	if not B64I then
		B64I = {}
		for i = 1, #B64 do B64I[ssub(B64, i, i)] = i - 1 end
	end
	data = string.gsub(data, "[^" .. B64 .. "]", "")
	local out = {}
	for i = 1, #data, 4 do
		local a = B64I[ssub(data, i, i)] or 0
		local b = B64I[ssub(data, i + 1, i + 1)] or 0
		local c = B64I[ssub(data, i + 2, i + 2)]
		local d = B64I[ssub(data, i + 3, i + 3)]
		local n = a * 262144 + b * 4096 + (c or 0) * 64 + (d or 0)
		out[#out + 1] = schar(math.floor(n / 65536) % 256)
		if c then out[#out + 1] = schar(math.floor(n / 256) % 256) end
		if d then out[#out + 1] = schar(n % 256) end
	end
	return tconcat(out)
end

-- convenience: encrypt a plaintext to a portable token (b64(xor(data,key)))
function Crypt.seal(plaintext, key)
	return Crypt.b64encode(Crypt.xor(plaintext, key))
end
function Crypt.open(token, key)
	return Crypt.xor(Crypt.b64decode(token), key)
end

return Crypt

end)()
local Secure = (function()
--!nonstrict
-- ============================================================================
--  Secure.lua  --  capture real executor functions & expose protected proxies
--
--  THE CORE PROTECTION. At load time (before any spy can install hooks) we grab
--  references to the real executor functions into PRIVATE upvalues, then hand
--  the wrapped script only thin proxies. Because the proxies call the captured
--  originals directly, a spy that later hooks the GLOBAL `request` / `http` /
--  `readfile` never sees the script's calls -- they bypass the global.
--
--  Proxies are wrapped with newcclosure so they read as native C-closures:
--  iscclosure() passes, and getupvalues() is blocked on them by most executors,
--  hiding the captured originals from getgc/upvalue inspection.
-- ============================================================================

local Secure = {}

-- resolve the real global table as early as possible
local realG = (getgenv and getgenv()) or (getfenv and getfenv(0)) or _G
local rawget, rawset = rawget, rawset
local iscc = iscclosure
local newcc = newcclosure or function(f) return f end
local clonef = clonefunction or function(f) return f end

-- list of sensitive globals we proxy. (function-valued globals only)
local CAPTURE = {
	"request", "http_request", "readfile", "writefile", "appendfile", "isfile",
	"isfolder", "listfiles", "makefolder", "delfile", "delfolder", "loadstring",
	"getgenv", "getrawmetatable", "setrawmetatable", "hookfunction", "hookmetamethod",
	"newcclosure", "getnamecallmethod", "setclipboard", "queue_on_teleport",
	"getcustomasset", "fireclickdetector", "firetouchinterest", "fireproximityprompt",
	"isexecutorclosure", "checkcaller", "getconnections", "getcallingscript",
}

-- Capture the real functions. Returns a PRIVATE table (kept as an upvalue by the
-- caller -- never store this in a global).
function Secure.capture()
	local raw = {}

	-- http via the common executor spellings, in priority order
	raw.http = (syn and syn.request) or (http and http.request) or http_request or request
	-- guard: if http appears already hooked (became an l-closure), remember it
	raw.http_tampered = (iscc and raw.http and not iscc(raw.http)) or false

	for _, name in ipairs(CAPTURE) do
		local fn = rawget(realG, name)
		if type(fn) == "function" then
			-- clone where supported so even a later identity-swap of the global
			-- can't reach our reference
			local ok, c = pcall(clonef, fn)
			raw[name] = ok and c or fn
			raw[name .. "_genuine"] = (iscc and iscc(fn)) or false
		end
	end

	-- HttpGet/HttpGetAsync live on `game`; capture bound callers
	local okGame = pcall(function() return game and game.HttpGet end)
	if okGame and game then
		raw.HttpGet = function(url, ...) return game:HttpGet(url, ...) end
		raw.HttpGetAsync = function(url, ...) return game:HttpGetAsync(url, ...) end
	end

	return raw
end

-- Build the proxy table the sandbox exposes. `raw` is the private capture.
-- Each proxy is a newcclosure so its upvalues (the real fn) are not inspectable.
function Secure.proxies(raw)
	local P = {}

	local function wrap(realFn)
		if type(realFn) ~= "function" then return nil end
		return newcc(function(...) return realFn(...) end)
	end

	-- generic passthrough proxies
	for _, name in ipairs(CAPTURE) do
		if raw[name] then P[name] = wrap(raw[name]) end
	end

	-- unified HTTP proxy (the prime spy target). Accepts the standard {Url=...}.
	if raw.http then
		local http = raw.http
		P.request = newcc(function(opts) return http(opts) end)
		P.http_request = P.request
		if syn then P.syn = { request = P.request } end
	end
	if raw.HttpGet then
		P.HttpGet = newcc(function(url, ...) return raw.HttpGet(url, ...) end)
		P.HttpGetAsync = newcc(function(url, ...) return raw.HttpGetAsync(url, ...) end)
	end

	return P
end

-- Snapshot identities so Integrity can detect later replacement of our proxies.
function Secure.fingerprint(P)
	local fp = {}
	for k, v in pairs(P) do
		if type(v) == "function" then fp[k] = v end
	end
	return fp
end

return Secure

end)()
local Environment = (function()
--!nonstrict
-- ============================================================================
--  Environment.lua  --  the sealed sandbox the wrapped script runs inside
--
--  Builds a custom _ENV whose:
--    * function-valued executor globals resolve to PROTECTED PROXIES
--    * everything else falls through to the real globals (so game, workspace,
--      Instance, math, string, task, etc. all work -- full Luau semantics)
--    * writes stay local to the sandbox (script can't pollute real _G)
--    * the metatable is private (Integrity verifies it wasn't swapped)
--
--  This is the isolation layer: the script believes it has a normal global
--  environment, but its sensitive calls are routed through the Vm.
-- ============================================================================

local Environment = {}

function Environment.build(proxies, realG)
	realG = realG or (getgenv and getgenv()) or _G

	-- the sandbox's own storage for globals the script defines
	local store = {}

	-- private metatable (kept out of the sandbox; Integrity holds a ref)
	local mt = {}

	mt.__index = function(_, key)
		-- 1. protected proxy?
		local p = proxies[key]
		if p ~= nil then return p end
		-- 2. script-local global?
		local s = store[key]
		if s ~= nil then return s end
		-- 3. fall through to the real environment
		return realG[key]
	end

	mt.__newindex = function(_, key, value)
		-- keep all writes inside the sandbox (never touch real globals)
		store[key] = value
	end

	-- unique private lock token. __metatable makes getmetatable(env) return THIS
	-- (hiding the real mt) and makes setmetatable(env, ...) error -- so the env's
	-- metatable cannot be swapped. Integrity verifies this token is still in place.
	local lock = {}
	mt.__metatable = lock

	local env = setmetatable({}, mt)

	-- expose a sandboxed getfenv/getgenv so the script's own introspection
	-- returns the sandbox, not the real globals (don't leak the boundary)
	store.getgenv = function() return env end
	store._G = env
	store.shared = store.shared or {}

	return env, mt, store, lock
end

return Environment

end)()
local Integrity = (function()
--!nonstrict
-- ============================================================================
--  Integrity.lua  --  anti-tamper / anti-penetration
--
--  Verifies the runtime hasn't been hooked or swapped, both at startup and via
--  a background watchdog. On tamper it triggers a caller-supplied onTamper
--  (the Vm wipes the sandbox + halts).
--
--  Checks:
--   * capture genuineness   -- were the executor funcs already hooked at capture?
--   * proxy identity         -- have our proxies been replaced since fingerprint?
--   * env seal               -- is the sandbox __index/__newindex intact?
--   * hostile introspection  -- is something actively decompiling/hooking us?
--   * source checksum        -- does the protected payload still match?
-- ============================================================================

local Integrity = {}

local iscc = iscclosure
local getus = getupvalues or (debug and debug.getupvalues)

-- 1. Were any captured executor functions already hooks (l-closures) at capture?
function Integrity.checkCapture(raw)
	local suspicious = {}
	if raw.http_tampered then suspicious[#suspicious + 1] = "http" end
	for k, v in pairs(raw) do
		if string.sub(k, -8) == "_genuine" and v == false then
			suspicious[#suspicious + 1] = string.sub(k, 1, -9)
		end
	end
	return suspicious
end

-- 2. Our proxies must still be the exact functions we created.
function Integrity.checkProxies(P, fingerprint)
	for k, original in pairs(fingerprint) do
		if P[k] ~= original then return false, k end
	end
	return true
end

-- 3. The sandbox env metatable must be intact (not re-pointed to leak globals).
function Integrity.checkEnv(env, expectedMT)
	local mt = getmetatable(env)
	if mt ~= expectedMT then return false, "metatable" end
	return true
end

-- 4. Best-effort: detect if our own proxies have become inspectable (a sign a
--    de-hook tool unwrapped the cclosure). On a healthy executor getupvalues on
--    a newcclosure should be empty/blocked; non-empty => someone unwrapped it.
function Integrity.checkOpaque(P)
	if not getus then return true end
	for _, v in pairs(P) do
		if type(v) == "function" then
			local ok, ups = pcall(getus, v)
			if ok and type(ups) == "table" and next(ups) ~= nil then
				return false
			end
		end
	end
	return true
end

-- run all startup checks; returns ok, reason
function Integrity.startup(ctx)
	local sus = Integrity.checkCapture(ctx.raw)
	if #sus > 0 and ctx.strict then
		return false, "capture-hooked:" .. table.concat(sus, ",")
	end
	local okP, badKey = Integrity.checkProxies(ctx.proxies, ctx.fingerprint)
	if not okP then return false, "proxy-swapped:" .. tostring(badKey) end
	local okE, why = Integrity.checkEnv(ctx.env, ctx.envLock)
	if not okE then return false, "env-" .. tostring(why) end
	if not Integrity.checkOpaque(ctx.proxies) then return false, "opaque-broken" end
	return true
end

-- background watchdog: re-run cheap checks on an interval and self-destruct.
-- Spawns through the Memory scope (ctx.mem) so the thread is tracked and
-- cancelled on cleanup -- it can never leak past the script's lifetime.
function Integrity.watchdog(ctx, onTamper)
	local wait_ = (task and task.wait) or wait
	local body = function()
		while ctx.alive do
			wait_(ctx.interval or 2)
			if not ctx.alive then return end
			local okP, badKey = Integrity.checkProxies(ctx.proxies, ctx.fingerprint)
			local okE = Integrity.checkEnv(ctx.env, ctx.envLock)
			if not okP or not okE then
				ctx.alive = false
				pcall(onTamper, okP and "env" or ("proxy:" .. tostring(badKey)))
				return
			end
		end
	end
	if ctx.mem and ctx.mem.spawn then
		ctx.mem:spawn(body)
	else
		local spawn = (task and task.spawn) or spawn
		if spawn then spawn(body) end
	end
end

return Integrity

end)()
local Stealth = (function()
--!nonstrict
-- ============================================================================
--  Stealth.lua  --  comprehensive environment spoofing / anti-detection
--
--  Covers the full sUNC executor surface (docs.sunc.su). For each function an
--  anti-cheat could use to fingerprint the executor, detect hooks, or scan for
--  injected objects, we install a fake that answers "clean" -- while leaving the
--  function usable for everyone else.
--
--  Technique: hookfunction (rewrites the function OBJECT, so even a reference
--  the AC captured early is affected), replacement wrapped in newcclosure (stays
--  a C-closure -> passes iscclosure). Everything pcall-guarded; only spoofs what
--  the executor actually exposes.
--
--  HONEST: beats ACs that read these globals at runtime and trust them. Does NOT
--  beat an AC that ran fully before you, re-implements checks in its own VM, or
--  validates server-side. Raises the bar across games.
-- ============================================================================

local Stealth = {}

local realG = (getgenv and getgenv()) or (getfenv and getfenv(0)) or _G
local newcc = newcclosure or function(f) return f end
local clonef = clonefunction
local hookf = hookfunction
local cloneref_ = cloneref or function(x) return x end
local rawget, rawset = rawget, rawset

-- private registries (weak so we never pin objects alive)
local hiddenObjs = setmetatable({}, { __mode = "k" })  -- hide from gc/instance scans
local genuineFns = setmetatable({}, { __mode = "k" })  -- report as un-hooked / ours
local ourScripts = setmetatable({}, { __mode = "k" })  -- hide script bytecode/closure
local installed  = false

function Stealth.hide(o)        if o ~= nil then hiddenObjs[o] = true end return o end
function Stealth.markGenuine(f) if type(f) == "function" then genuineFns[f] = true end return f end
function Stealth.hideScript(s)  if s ~= nil then ourScripts[s] = true end return s end

-- ---- hook helpers ---------------------------------------------------------
-- CRITICAL: after hookfunction(real, repl), the `real` OBJECT behaves like repl.
-- So the replacement must NOT call `real` on its passthrough path (that would be
-- infinite recursion -> C stack overflow). We clone the original FIRST and have
-- the replacement call the unhooked clone. If we can't clone, we fall back to a
-- plain global swap (which leaves `real` itself untouched, so calling it is safe).
local function emplace(container, name, build)
	if type(container) ~= "table" then return end
	local real = rawget(container, name)
	if type(real) ~= "function" then return end
	if hookf and clonef then
		local okc, orig = pcall(clonef, real)
		if okc and type(orig) == "function" then
			local repl = newcc(build(orig))         -- repl -> clone (unhooked): safe
			genuineFns[repl] = true; hiddenObjs[repl] = true
			if pcall(hookf, real, repl) then return end
		end
	end
	-- fallback: global/table swap, repl -> real (real is NOT hooked here): safe
	local repl = newcc(build(real))
	genuineFns[repl] = true; hiddenObjs[repl] = true
	pcall(rawset, container, name, repl)
end

local function spoof(name, build)            emplace(realG, name, build) end
local function spoofIn(tbl, name, build)     emplace(tbl, name, build) end

-- filter our hidden/genuine objects out of an array-like result table.
local function filterArray(t)
	if type(t) ~= "table" then return t end
	local out = {}
	for i = 1, #t do
		local v = t[i]
		if not (hiddenObjs[v] or genuineFns[v]) then out[#out + 1] = v end
	end
	return out
end

-- ===========================================================================
function Stealth.install(opts)
	if installed then return end
	installed = true
	opts = opts or {}
	local fakeName = opts.spoofName            -- nil => "no executor"
	local fakeVer  = opts.spoofVersion or "1.0.0"

	-- DISGUISE: a real game LocalScript (cloneref'd) to report as the "calling
	-- script", so introspection sees a legit script instead of getcallingscript()
	-- == nil (which screams "injected"). On by default; opts.disguise=false to skip.
	local decoyScript = nil
	if opts.disguise ~= false then
		pcall(function()
			local lp = game:GetService("Players").LocalPlayer
			local char = lp and lp.Character
			decoyScript = (char and char:FindFirstChild("Animate"))
				or (lp and lp:FindFirstChildWhichIsA("LocalScript", true))
		end)
		if decoyScript then pcall(function() decoyScript = cloneref_(decoyScript) end) end
	end

	-- 1) IDENTITY ----------------------------------------------------------
	for _, n in ipairs({ "identifyexecutor", "getexecutorname", "iexecutor" }) do
		spoof(n, function() return function()
			if fakeName then return fakeName, fakeVer end
			return nil
		end end)
	end

	-- 2) CLOSURE CHECKS ----------------------------------------------------
	spoof("iscclosure",       function(r) return function(f) if genuineFns[f] then return true  end return r(f) end end)
	spoof("isexecutorclosure",function(r) return function(f) if genuineFns[f] then return false end return r(f) end end)
	spoof("isourclosure",     function(r) return function(f) if genuineFns[f] then return false end return r(f) end end)
	spoof("islclosure",       function(r) return function(f) if genuineFns[f] then return false end return r(f) end end)
	spoof("checkcaller",      function(r) return function() return false end end)
	-- stable fake hash for our funcs so repeated checks stay consistent
	spoof("getfunctionhash",  function(r) return function(f) if genuineFns[f] then return "00000000000000000000000000000000" end return r(f) end end)

	-- 3) ENVIRONMENT / GC scans -- strip our objects ----------------------
	spoof("getgc",     function(r) return function(...) return filterArray(r(...)) end end)
	spoof("filtergc",  function(r) return function(...) local t = r(...) return type(t)=="table" and filterArray(t) or t end end)
	spoof("getreg",    function(r) return function(...) return filterArray(r(...)) end end)
	-- getgenv/getrenv must keep identity (callers rely on it); objects already hidden via getgc

	-- 4) INSTANCE scans -- strip our injected instances -------------------
	spoof("getinstances",    function(r) return function(...) return filterArray(r(...)) end end)
	spoof("getnilinstances", function(r) return function(...) return filterArray(r(...)) end end)

	-- 5) SCRIPT scans -- hide our scripts/closures ------------------------
	spoof("getloadedmodules", function(r) return function(...) return filterArray(r(...)) end end)
	spoof("getrunningscripts",function(r) return function(...) return filterArray(r(...)) end end)
	spoof("getscripts",       function(r) return function(...) return filterArray(r(...)) end end)
	spoof("getcallingscript", function(r) return function(...) local s = r(...); if ourScripts[s] or s == nil then return decoyScript end return s end end)
	spoof("getscriptbytecode",function(r) return function(s, ...) if ourScripts[s] then return nil end return r(s, ...) end end)
	spoof("getscriptclosure", function(r) return function(s, ...) if ourScripts[s] then return nil end return r(s, ...) end end)
	spoof("getscripthash",    function(r) return function(s, ...) if ourScripts[s] then return "" end return r(s, ...) end end)
	spoof("getsenv",          function(r) return function(s, ...) if ourScripts[s] then return nil end return r(s, ...) end end)

	-- 6) DEBUG introspection -- blank out for OUR functions ---------------
	if debug then
		spoofIn(debug, "getupvalue",  function(r) return function(f, ...) if genuineFns[f] then return nil end return r(f, ...) end end)
		spoofIn(debug, "getupvalues", function(r) return function(f, ...) if genuineFns[f] then return {}  end return r(f, ...) end end)
		spoofIn(debug, "getconstant", function(r) return function(f, ...) if genuineFns[f] then return nil end return r(f, ...) end end)
		spoofIn(debug, "getconstants",function(r) return function(f, ...) if genuineFns[f] then return {}  end return r(f, ...) end end)
		spoofIn(debug, "getproto",    function(r) return function(f, ...) if genuineFns[f] then return nil end return r(f, ...) end end)
		spoofIn(debug, "getprotos",   function(r) return function(f, ...) if genuineFns[f] then return {}  end return r(f, ...) end end)
	end
	-- top-level mirrors (some executors expose these globally too)
	for _, n in ipairs({ "getupvalue","getupvalues","getconstant","getconstants","getproto","getprotos" }) do
		spoof(n, function(r) return function(f, ...)
			if genuineFns[f] then
				if string.sub(n, -1) == "s" then return {} end
				return nil
			end
			return r(f, ...)
		end end)
	end

	-- 7) common executor extras (Volt/Synapse/etc. spellings that may exist) ----
	for _, n in ipairs({ "getexecutorname", "getexecutor", "getexecutorinfo" }) do
		spoof(n, function() return function()
			if fakeName then return fakeName, fakeVer end
			return nil
		end end)
	end
	-- decompiler-style probes: refuse on our scripts
	for _, n in ipairs({ "decompile", "disassemble", "dumpstring" }) do
		spoof(n, function(r) return function(s, ...) if ourScripts[s] then return "" end return r(s, ...) end end)
	end

	-- 7b) Potassium / extended closure + thread + hook checks --------------
	-- the big one: isfunctionhooked must say NO for the funcs your cheat hooks
	spoof("isfunctionhooked", function(r) return function(f, ...) if genuineFns[f] then return false end return r(f, ...) end end)
	spoof("isnewcclosure",    function(r) return function(f, ...) if genuineFns[f] then return false end return r(f, ...) end end)
	spoof("isourclosure",     function(r) return function(f, ...) if genuineFns[f] then return false end return r(f, ...) end end)
	-- "is this the executor / a hook thread" -> no
	spoof("isourthread",      function(r) return function() return false end end)
	-- thread/script linkage: don't reveal our scripts
	spoof("getscriptfromthread", function(r) return function(t, ...) local s = r(t, ...) if ourScripts[s] then return nil end return s end end)
	spoof("getscriptthread",     function(r) return function(s, ...) if ourScripts[s] then return nil end return r(s, ...) end end)
	spoof("gettenv",             function(r) return function(s, ...) if ourScripts[s] then return nil end return r(s, ...) end end)

	-- Potassium oth.* (original-thread hooking) table
	local oth = rawget(realG, "oth")
	if type(oth) == "table" then
		spoofIn(oth, "is_hook_thread", function(r) return function() return false end end)
	end

	-- debug.* extras present on Potassium
	if debug then
		spoofIn(debug, "getcallstack", function(r) return function(...) return r(...) end end)  -- seam: frames aren't our objects
		-- getregistry: return a filtered COPY with our objects removed (AC scans are read-only)
		spoofIn(debug, "getregistry", function(r) return function(...)
			local reg = r(...)
			if type(reg) ~= "table" then return reg end
			local out = {}
			for k, v in pairs(reg) do
				if not (hiddenObjs[k] or hiddenObjs[v] or genuineFns[k] or genuineFns[v]) then
					out[k] = v
				end
			end
			return out
		end end)
		spoofIn(debug, "getinfo", function(r) return function(...) return r(...) end end)  -- seam
	end

	-- metatable seams: only safe to touch CONDITIONALLY. We do NOT blanket-fake
	-- getrawmetatable/getnamecallmethod -- faking the real game metatable breaks
	-- everything. If YOUR cheat hooks __namecall, register the clean function via
	-- Stealth.markGenuine(yourHook) and add a targeted getrawmetatable spoof.

	-- 8) USER-SUPPLIED EXTENSIONS (add Volt-specific names without editing code) -
	--    opts.identity   = { "voltname", ... }     -> spoofed like identifyexecutor
	--    opts.gcFilters  = { "somelist", ... }     -> array results have our objs removed
	--    opts.genuine    = { "iscustom", ... }     -> return clean for our funcs
	--    opts.scriptHide = { "getbytecode2", ... } -> return nothing for our scripts
	for _, n in ipairs(opts.identity or {}) do
		spoof(n, function() return function() if fakeName then return fakeName, fakeVer end return nil end end)
	end
	for _, n in ipairs(opts.gcFilters or {}) do
		spoof(n, function(r) return function(...) local t = r(...) return type(t)=="table" and filterArray(t) or t end end)
	end
	for _, n in ipairs(opts.genuine or {}) do
		spoof(n, function(r) return function(f, ...) if genuineFns[f] then return false end return r(f, ...) end end)
	end
	for _, n in ipairs(opts.scriptHide or {}) do
		spoof(n, function(r) return function(s, ...) if ourScripts[s] then return nil end return r(s, ...) end end)
	end

	return true
end

return Stealth

end)()
local Memory = (function()
--!nonstrict
-- ============================================================================
--  Memory.lua  --  resource scope + leak/overflow protection
--
--  Every thread, connection and disposable the VM creates is registered in a
--  scope. When the script ends (return, error, or tamper) the scope is torn down
--  deterministically: threads cancelled, connections disconnected, tables
--  cleared, GC forced. Plus a budget guard that collects GC the moment memory
--  crosses a threshold, so a runaway/hostile script can't balloon the VM.
--
--  Design notes:
--   * Registries that hold game objects use WEAK keys so they never pin memory.
--   * The scope holds STRONG refs to threads/connections (so it can cancel them)
--     but cleanup is GUARANTEED to run, bounding their lifetime.
--   * Counters are capped; nothing grows unbounded.
-- ============================================================================

local Memory = {}
Memory.__index = Memory

local taskLib   = task
local taskSpawn = (taskLib and taskLib.spawn) or spawn
local taskWait  = (taskLib and taskLib.wait) or wait
local taskDefer = (taskLib and taskLib.defer) or taskSpawn
local taskCancel = taskLib and taskLib.cancel
local cg = collectgarbage

local MAX_TRACKED = 4096   -- hard cap so the bookkeeping itself can't leak

function Memory.new()
	return setmetatable({
		alive = true,
		threads = {},
		conns = {},
		disposers = {},
		count = 0,
	}, Memory)
end

local function bounded(self)
	return self.count < MAX_TRACKED
end

-- spawn a tracked thread (auto-cancelled on cleanup)
function Memory:spawn(fn)
	if not self.alive or not bounded(self) then return end
	local co = taskSpawn(fn)
	self.threads[#self.threads + 1] = co
	self.count = self.count + 1
	return co
end

-- track an arbitrary resource with a disposer
function Memory:track(obj, dispose)
	if not self.alive or not bounded(self) then return obj end
	if dispose then
		self.disposers[#self.disposers + 1] = dispose
		self.count = self.count + 1
	end
	return obj
end

-- track a signal connection (auto-disconnected on cleanup)
function Memory:connect(signal, fn)
	if not self.alive or not bounded(self) then return end
	local ok, c = pcall(function() return signal:Connect(fn) end)
	if ok and c then
		self.conns[#self.conns + 1] = c
		self.count = self.count + 1
		return c
	end
end

-- deterministic teardown -- safe to call multiple times
function Memory:cleanup()
	if not self.alive then return end
	self.alive = false
	for _, c in ipairs(self.conns) do
		pcall(function() if c.Disconnect then c:Disconnect() elseif c.disconnect then c:disconnect() end end)
	end
	if taskCancel then
		for _, co in ipairs(self.threads) do pcall(taskCancel, co) end
	end
	for _, d in ipairs(self.disposers) do pcall(d) end
	self.conns, self.threads, self.disposers, self.count = {}, {}, {}, 0
	if cg then pcall(cg, "collect") end
end

-- memory-budget guard: force GC when usage crosses the threshold; if it stays
-- over after a collect, escalate to onOverflow (the Vm halts).
function Memory:guard(opts)
	opts = opts or {}
	local budgetKB = opts.budgetKB or 700000   -- ~700 MB ceiling by default
	local interval = opts.interval or 4
	self:spawn(function()
		while self.alive do
			taskWait(interval)
			if not self.alive then return end
			local used = cg and cg("count") or 0     -- KB
			if used > budgetKB then
				if cg then pcall(cg, "collect") end
				used = cg and cg("count") or 0
				if used > budgetKB and opts.onOverflow then
					pcall(opts.onOverflow, used)
					return
				end
			end
		end
	end)
end

return Memory

end)()
local Defense = (function()
--!nonstrict
-- ============================================================================
--  Defense.lua  --  detect tools SPYING on your script (anti-tamper)
--
--  These detect OTHER exploiters' inspection tools so your script can react
--  (halt / hide) before its logic or remotes are stolen:
--    * HTTP spy      -- request/http hooked (closure-type check vs captured original)
--    * namecall hook -- __namecall identity changed (IY-style stack inspection)
--    * remote spy    -- gcinfo spike on FireServer (spies deep-clone args)  [opt-in]
--    * Dex explorer  -- weak-table service-cache persistence                [opt-in]
--
--  IMPORTANT: this is ANTI-SPY (protect your code from other exploiters), NOT
--  anti-cheat. It does nothing against the GAME's AC -- and the remote/dex probes
--  even ADD client AC surface (they fire a remote / force GC). Keep those opt-in.
-- ============================================================================

local Defense = {}

local gcinfo_   = gcinfo or function() return (collectgarbage and collectgarbage("count")) or 0 end
local cloneref_ = cloneref or function(x) return x end
local collect   = collectgarbage
local iscc      = iscclosure       -- captured at load; Stealth passes through for non-ours
local dbinfo    = debug and debug.info

-- 1) HTTP spy: a spy hooks the global request -> it becomes an l-closure -------
-- get the real __namecall fn via an errored game:IsA() ----------------------
local function actualNamecall()
	local nc, caller
	if not dbinfo then return nil end
	xpcall(function() return game:IsA() end, function()
		nc, caller = dbinfo(2, "f"), dbinfo(3, "f")
	end)
	return nc, caller
end

local function remoteSpike()
	local ok, spike = pcall(function()
		local re = Instance.new("RemoteEvent")
		local payload = { 1, 2, 3, { nested = true }, "probe" }
		local before = gcinfo_()
		pcall(function() re:FireServer(payload) end)
		local after = gcinfo_()
		pcall(function() re:Destroy() end)
		return after - before
	end)
	return (ok and type(spike) == "number") and spike or 0
end

-- BASELINE: snapshot the environment AFTER your script has set up its own hooks,
-- so YOUR hooks are treated as "normal". Only CHANGES after this (a spy) trigger.
-- Until baseline() is called, the change-detectors stay silent (no false positives).
Defense._snap = nil
function Defense.baseline()
	local realG = (getgenv and getgenv()) or _G
	Defense._snap = {
		ready = true,
		nc = (actualNamecall()),
		request = rawget(realG, "request"),
		http_request = rawget(realG, "http_request"),
		getgc = rawget(realG, "getgc"),     -- a dumper re-hooking getgc -> identity change
		spike = remoteSpike(),
	}
	return true
end

-- getgc-scan: someone re-hooked getgc (a memory scanner/dumper) after baseline
function Defense.detectGetgcHook()
	local s = Defense._snap
	if not (s and s.ready) then return false end
	local realG = (getgenv and getgenv()) or _G
	local cur = rawget(realG, "getgc")
	if cur and s.getgc and cur ~= s.getgc then return true, "getgc re-hooked (memory scan)" end
	return false
end

-- spy-tool GLOBALS (Hydroxide/SimpleSpy/etc. set flags or tables in getgenv)
local SPY_GLOBALS = { "Hydroxide", "oh_load", "SimpleSpy", "SimpleSpyExecuted", "RemoteSpyV3", "IY_LOADED" }
function Defense.detectSpyGlobals()
	local ok, g = pcall(getgenv)
	if ok and type(g) == "table" then
		for _, n in ipairs(SPY_GLOBALS) do
			if rawget(g, n) ~= nil then return true, "global " .. n end
		end
	end
	return false
end

-- 1) HTTP spy: the request function IDENTITY changed since baseline (newly hooked)
function Defense.detectHttpSpy()
	local s = Defense._snap
	if not (s and s.ready) then return false end
	local realG = (getgenv and getgenv()) or _G
	for _, n in ipairs({ "request", "http_request" }) do
		local cur = rawget(realG, n)
		if cur and s[n] and cur ~= s[n] then return true, n .. " changed after baseline" end
	end
	return false
end

-- 2) namecall hook: __namecall identity changed since baseline
function Defense.detectNamecallHook()
	local s = Defense._snap
	if not (s and s.ready) then return false end
	local nc = actualNamecall()
	if s.nc and nc and nc ~= s.nc then return true, "__namecall changed after baseline" end
	return false
end

-- 3) remote spy: gc spike on FireServer rose ABOVE the baseline (a new arg-cloner)
function Defense.detectRemoteSpy()
	local s = Defense._snap
	if not (s and s.ready) then return false end
	local spike = remoteSpike()
	if spike > (s.spike or 0) + 64 then
		return true, "FireServer gc spike " .. tostring(spike)
	end
	return false
end

-- 4a) Infinite Yield (and similar admin tools) set a known global flag --------
function Defense.detectInfiniteYield()
	local ok, g = pcall(getgenv)
	if ok and type(g) == "table" then
		if rawget(g, "IY_LOADED") == true then return true, "Infinite Yield" end
	end
	return false
end

-- 4b) Spy/explorer GUIs (Dex, RemoteSpy, SimpleSpy, Hydroxide, IY window) ------
-- scans CoreGui, the executor-hidden gui (gethui), and PlayerGui by exact name.
-- PRECISE name matching: exact known names, plus controlled version patterns,
-- so we don't false-positive on legit GUIs (e.g. "Dexterity" must NOT match "dex").
local EXACT = {
	["dex"] = true, ["dex explorer"] = true, ["remotespy"] = true, ["remote spy"] = true,
	["simplespy"] = true, ["simple spy"] = true, ["hydroxide"] = true,
}
local function isSpyName(nm)
	if EXACT[nm] then return true end
	if string.match(nm, "^dex%s*v?%d") then return true end          -- "dex v4", "dex 5"
	if string.match(nm, "^remotespy") then return true end
	if string.match(nm, "^simplespy") then return true end
	if string.match(nm, "^hydroxide") then return true end
	return false
end
function Defense.detectSpyGui()
	local parents = {}
	pcall(function() parents[#parents + 1] = game:GetService("CoreGui") end)
	if gethui then pcall(function() parents[#parents + 1] = gethui() end) end
	pcall(function()
		local pg = game:GetService("Players").LocalPlayer:FindFirstChild("PlayerGui")
		if pg then parents[#parents + 1] = pg end
	end)
	for _, p in ipairs(parents) do
		local ok, kids = pcall(function() return p:GetChildren() end)
		if ok then
			for _, c in ipairs(kids) do
				if isSpyName(string.lower(c.Name)) then return true, "GUI: " .. c.Name end
			end
		end
	end
	return false
end

-- 4) Dex: it strong-caches services, so a weak ref survives a forced GC -------
function Defense.detectDex()
	local ok, persisted = pcall(function()
		local weak = setmetatable({}, { __mode = "v" })
		weak[1] = cloneref_(game:GetService("TestService"))
		weak[1] = weak[1]   -- (kept only in the weak table after this scope)
		if collect then for _ = 1, 3 do pcall(collect, "collect") end end
		return weak[1] ~= nil
	end)
	return ok and persisted == true
end

-- SaveInstance guard: hook saveinstance-family so a game/script DUMP is caught
-- the moment it's attempted. Call once (from the watchdog) with the reaction.
function Defense.installSaveGuard(onDetect)
	local realG = (getgenv and getgenv()) or _G
	local newcc_ = newcclosure or function(f) return f end
	local hookf, clonef = hookfunction, clonefunction
	for _, n in ipairs({ "saveinstance", "synsaveinstance", "SaveInstance", "saveplace" }) do
		local f = rawget(realG, n)
		if type(f) == "function" and hookf and clonef then
			local ok, orig = pcall(clonef, f)
			if ok then
				pcall(hookf, f, newcc_(function(...)
					pcall(onDetect, "saveinstance", n)
					return orig(...)
				end))
			end
		end
	end
end

-- run a scan; returns array of { name = , detail = }
function Defense.scan(opts)
	opts = opts or {}
	local found = {}
	local function run(enabled, fn, name, arg)
		if not enabled then return end
		local ok, detail = fn(arg)
		if ok then found[#found + 1] = { name = name, detail = detail or "" } end
	end
	run(opts.iy ~= false,        Defense.detectInfiniteYield, "infinite-yield")
	run(opts.gui ~= false,       Defense.detectSpyGui,        "spy-gui")     -- Dex/RemoteSpy/IY window
	run(opts.globals ~= false,   Defense.detectSpyGlobals,    "spy-global")  -- Hydroxide/SimpleSpy/etc.
	run(opts.http ~= false,      Defense.detectHttpSpy,       "http-spy")
	run(opts.namecall ~= false,  Defense.detectNamecallHook,  "namecall-hook")
	run(opts.getgc ~= false,     Defense.detectGetgcHook,     "getgc-scan")  -- dumper re-hooked getgc
	run(opts.remote == true,     Defense.detectRemoteSpy,     "remote-spy")  -- opt-in (fires a remote)
	run(opts.dex == true,        Defense.detectDex,           "dex")         -- opt-in (forces GC)
	return found
end

-- watchdog: scan promptly then on an interval; call onDetect on first hit.
-- Light probes (IY/GUI/http/namecall) run every tick; HEAVY probes (remote gc
-- spike, Dex weak-table) run only every Nth tick so they don't spam remote-fires
-- or force GC constantly. Heavy probes are ON unless explicitly set to false.
function Defense.watchdog(ctx, onDetect, opts)
	opts = opts or {}
	-- proactive SaveInstance dump guard (fires the moment a dump is attempted)
	pcall(Defense.installSaveGuard, onDetect)
	local body = function()
		local wait_ = (task and task.wait) or wait
		wait_(opts.startDelay or 1)            -- let tools finish loading
		-- reliable signals (IY global, Dex/spy GUI by name, http hook, namecall hook)
		-- react on the FIRST hit. Only the noisy probes need a 2nd confirmation.
		local NOISY = { ["remote-spy"] = true, ["dex"] = true }
		local n, lastHit, confirm = 0, nil, 0
		-- baseline after a grace period so the script's OWN hooks aren't flagged
		-- (Vm also baselines right after the main chunk; whichever fires first wins).
		local graceUntil = (tick and tick() or 0) + (opts.gracePeriod or 4)
		while ctx.alive do
			n = n + 1
			if not (Defense._snap and Defense._snap.ready) and (tick and tick() or 0) >= graceUntil then
				pcall(Defense.baseline)
			end
			local heavy = (n % (opts.heavyEvery or 5)) == 0
			local hits = Defense.scan({
				iy = opts.iy, gui = opts.gui, globals = opts.globals,
				http = opts.http, namecall = opts.namecall, getgc = opts.getgc,
				remote = (opts.remote ~= false) and heavy,   -- throttled, on by default
				dex = (opts.dex ~= false) and heavy,           -- throttled, on by default
				raw = ctx.raw,
			})
			if #hits > 0 then
				local h = hits[1]
				local need = NOISY[h.name] and 2 or 1        -- reliable = instant, noisy = confirm twice
				if h.name == lastHit then confirm = confirm + 1
				else lastHit, confirm = h.name, 1 end
				if confirm >= need then
					pcall(onDetect, h.name, h.detail)
					return
				end
			else
				lastHit, confirm = nil, 0
			end
			wait_(opts.interval or 3)
		end
	end
	if ctx.mem and ctx.mem.spawn then ctx.mem:spawn(body)
	else local s = (task and task.spawn) or spawn if s then s(body) end end
end

return Defense

end)()
local Neuter = (function()
--!nonstrict
-- ============================================================================
--  Neuter.lua  --  best-effort anti-cheat neutralizer (with honest reporting)
--
--  Attempts, in order, every CLIENT-SIDE technique to blind an AC, and REPORTS
--  the outcome of each. If it can't bypass, it says so loudly:
--      "AC bypass fail (error; <reason>)"
--  rather than silently pretending you're undetected.
--
--  Strategies:
--    1. global-spoof   -- replace detection globals with clean-answering versions
--    2. upvalue-patch  -- find ACs that captured detection fns as upvalues and
--                         debug.setupvalue them to our clean versions
--    3. table-patch    -- replace detection fns held in (writable) state tables
--                         (reaches some VM-style ACs)
--    4. report-block   -- best-effort: neutralize the global HTTP request path
--
--  HARD TRUTH (always reported): this is CLIENT-SIDE only. An AC that is
--  VM-obfuscated (functions buried in encrypted state -> nothing to patch) or
--  that validates SERVER-SIDE cannot be bypassed from here. Rivals is both.
-- ============================================================================

local Neuter = {}

local newcc   = newcclosure or function(f) return f end
local getgc_  = getgc
local getups  = getupvalues or (debug and debug.getupvalues)
local setup   = debug and debug.setupvalue
local realG   = (getgenv and getgenv()) or _G
local rawget, rawset = rawget, rawset

local SCAN_CAP = 300000

-- clean-answering replacements: AC sees "no executor, nothing hooked"
local function replacements()
	local R = {}
	R.identifyexecutor   = newcc(function() return nil end)
	R.getexecutorname    = newcc(function() return nil end)
	R.getexecutor        = newcc(function() return nil end)
	R.iscclosure         = newcc(function() return true end)   -- everything looks native
	R.isexecutorclosure  = newcc(function() return false end)
	R.isourclosure       = newcc(function() return false end)
	R.islclosure         = newcc(function() return false end)
	R.isfunctionhooked   = newcc(function() return false end)
	R.checkcaller        = newcc(function() return false end)
	R.isourthread        = newcc(function() return false end)
	return R
end

-- map ORIGINAL function identity -> replacement (for patching captured refs)
local function identityMap(R)
	local m = {}
	for name, repl in pairs(R) do
		local orig = rawget(realG, name)
		if type(orig) == "function" then m[orig] = repl end
	end
	return m
end

-- 1) global spoof -----------------------------------------------------------
function Neuter.globalSpoof(R)
	local n = 0
	for name, repl in pairs(R) do
		if type(rawget(realG, name)) == "function" then
			if hookfunction and clonefunction then
				local ok, orig = pcall(clonefunction, rawget(realG, name))
				if ok then pcall(hookfunction, rawget(realG, name), repl) else pcall(rawset, realG, name, repl) end
			else
				pcall(rawset, realG, name, repl)
			end
			n = n + 1
		end
	end
	return n > 0, "spoofed " .. n .. " globals", 0
end

-- 2) upvalue patch ----------------------------------------------------------
function Neuter.patchUpvalues(idmap)
	if not (getgc_ and getups and setup) then return false, "no getgc/debug.setupvalue" end
	local patched, scanned = 0, 0
	pcall(function()
		for _, fn in ipairs(getgc_(false) or getgc_()) do
			if scanned > SCAN_CAP then break end
			scanned = scanned + 1
			if type(fn) == "function" then
				local oku, ups = pcall(getups, fn)
				if oku and type(ups) == "table" then
					for i, uv in pairs(ups) do
						if idmap[uv] then
							if pcall(setup, fn, i, idmap[uv]) then patched = patched + 1 end
						end
					end
				end
			end
		end
	end)
	return patched > 0, "patched " .. patched .. " captured upvalue(s) of " .. scanned .. " closures", patched
end

-- 3) table patch (reaches some VM-style ACs that read fns from state tables) -
function Neuter.patchTables(idmap)
	if not getgc_ then return false, "no getgc" end
	local patched, scanned = 0, 0
	pcall(function()
		for _, t in ipairs(getgc_(true)) do
			if scanned > SCAN_CAP then break end
			scanned = scanned + 1
			if type(t) == "table" then
				pcall(function()
					for k, v in pairs(t) do
						if idmap[v] then
							if pcall(function() t[k] = idmap[v] end) then patched = patched + 1 end
						end
					end
				end)
			end
		end
	end)
	return patched > 0, "patched " .. patched .. " table slot(s)", patched
end

-- 4) report block (best-effort) --------------------------------------------
function Neuter.blockReporting()
	-- We can only neutralize a report path we can see. The global request is
	-- proxied by Secure already; an AC-internal report channel inside a VM is
	-- not generically locatable, so report this honestly.
	return false, "report channel not generically locatable (AC-internal)"
end

-- orchestrate ---------------------------------------------------------------
function Neuter.run(opts)
	opts = opts or {}
	local logf = opts.log or function(m) pcall(warn, m) end
	local R = replacements()
	local idmap = identityMap(R)

	local results, patched = {}, 0
	local function strat(name, fn, ...)
		local ok, detail, n = fn(...)
		results[#results + 1] = { name = name, ok = ok, detail = detail }
		if type(n) == "number" then patched = patched + n end
		logf("[Neuter] " .. name .. ": " .. (ok and "OK" or "FAIL") .. " -- " .. tostring(detail))
	end

	strat("global-spoof",  Neuter.globalSpoof, R)
	strat("upvalue-patch", Neuter.patchUpvalues, idmap)
	strat("table-patch",   Neuter.patchTables, idmap)
	strat("report-block",  Neuter.blockReporting)

	-- VERDICT (honest)
	local verdict
	if patched > 0 then
		verdict = "client checks neutralized (" .. patched .. " refs patched). "
			.. "WARNING: server-side validation is NOT affected -- this is not full immunity."
		logf("[Neuter] result: PARTIAL -- " .. verdict)
	else
		verdict = "no patchable detection refs found -- AC is VM-obfuscated/absent or "
			.. "captures privately; nothing to neutralize client-side."
		logf("AC bypass fail (error; " .. verdict .. ")")
	end

	return { patched = patched, results = results, ok = patched > 0, verdict = verdict }
end

return Neuter

end)()
local License = (function()
--!nonstrict
-- ============================================================================
--  License.lua  --  key / HWID whitelist, expiry, server validation, delivery
--
--  Anti-leak core. A protected script can require a valid KEY (+ optional HWID
--  lock) before it runs, enforce an EXPIRY, and/or fetch its real payload from
--  YOUR server only after the key checks out (so a leaked file is useless).
--
--  Validation order (any you configure):
--    1. expiry      -- refuse if past opts.expiry (server time when possible)
--    2. local keys  -- opts.keys = { "KEY1", ... } embedded allow-list
--    3. server      -- GET opts.endpoint?key=..&hwid=..  -> body must contain "ok"
--  If none configured, it allows (no license).
-- ============================================================================

local License = {}

local function httpGet(url)
	local fns = {
		function() return game:HttpGetAsync(url) end,
		function() return game:HttpGet(url) end,
		function() return request and request({ Url = url, Method = "GET" }).Body end,
	}
	for _, f in ipairs(fns) do
		local ok, body = pcall(f)
		if ok and type(body) == "string" then return body end
	end
	return nil
end

-- stable per-machine id
function License.hwid()
	local id
	pcall(function() id = (gethwid and gethwid()) or (get_hwid and get_hwid()) end)
	if not id then pcall(function() id = game:GetService("RbxAnalyticsService"):GetClientId() end) end
	return tostring(id or "unknown")
end

-- tamper-resistant time: try a web time source, fall back to os.time
function License.now()
	local body = httpGet("https://worldtimeapi.org/api/timezone/Etc/UTC.txt")
	if body then
		local ut = string.match(body, "unixtime:%s*(%d+)")
		if ut then return tonumber(ut) end
	end
	return os.time and os.time() or 0
end

local function inList(list, key)
	for _, k in ipairs(list) do if k == key then return true end end
	return false
end

-- returns ok, reason
function License.validate(opts)
	opts = opts or {}

	if opts.expiry then
		local now = License.now()
		if now and now > 0 and now > opts.expiry then
			return false, "license expired"
		end
	end

	if opts.endpoint then
		local hwid = License.hwid()
		local sep = string.find(opts.endpoint, "?", 1, true) and "&" or "?"
		local url = opts.endpoint .. sep .. "key=" .. tostring(opts.key or "")
			.. "&hwid=" .. hwid
		local body = httpGet(url)
		if not body then return false, "license server unreachable" end
		local lb = string.lower(body)
		if string.find(lb, "ok", 1, true) or string.find(lb, "valid", 1, true) then
			return true, "ok", body  -- body may carry the payload for server-delivery
		end
		return false, "key rejected by server"
	end

	if opts.keys then
		if opts.key and inList(opts.keys, opts.key) then return true, "ok" end
		return false, "invalid key"
	end

	return true, "no license configured"
end

-- SERVER-SIDE DELIVERY: validate, and if the server returns the (encrypted)
-- payload in its response, return it so the loader can run it. Body format the
-- reference server uses:  "ok\n<base64-xored-payload>"  (key is the xor key).
function License.deliver(opts)
	local ok, reason, body = License.validate(opts)
	if not ok then return nil, reason end
	if body then
		local nl = string.find(body, "\n", 1, true)
		if nl then return string.sub(body, nl + 1), "ok" end
	end
	return nil, "validated (no payload in response)"
end

return License

end)()
local Vm = (function()
--!nonstrict
-- ============================================================================
--  Vm.lua  --  main entry of the Vm protection runtime
--
--  Orchestrates Secure (capture+proxies), Environment (sandbox), and Integrity
--  (anti-tamper), then runs the wrapped script inside the sealed runtime.
--
--  API:
--    Vm.run(chunk [, opts])     -- chunk = source string OR a function
--    Vm.protect(fn [, opts])    -- returns a hardened wrapper of fn
--
--  opts = {
--    name     = "Sell a Lemon",      -- label for errors/telemetry
--    strict   = false,                -- abort if executor funcs look pre-hooked
--    interval = 2,                    -- watchdog period (seconds)
--    onTamper = function(reason) end, -- override default self-destruct
--    checksum = "<fnv hash>",         -- optional source integrity pin
--  }
-- ============================================================================

local Crypt       = Crypt
local Secure      = Secure
local Environment = Environment
local Integrity   = Integrity
local Stealth     = Stealth
local Memory      = Memory
local Defense     = Defense
local Neuter      = Neuter
local License     = License

local Vm = {}
Vm._VERSION = "1.0.0"

local realG = (getgenv and getgenv()) or (getfenv and getfenv(0)) or _G
local loadstr = loadstring or load
local setfenv_ = setfenv

-- default self-destruct: wipe the sandbox + raise, so a tampered run cannot
-- continue executing the protected logic.
local function defaultTamper(ctx, reason)
	ctx.alive = false
	-- neuter the proxies so any in-flight call resolves to nothing
	for k in pairs(ctx.proxies) do ctx.proxies[k] = nil end
	if ctx.mem then pcall(function() ctx.mem:cleanup() end) end  -- free threads/conns
	error("[Vm] integrity violation (" .. tostring(reason) .. ") -- halted", 0)
end

-- Build a fresh, sealed runtime context.
local function newContext(opts)
	-- install anti-detection FIRST (as early as we can), then hide our own
	-- objects from gc/closure scans so the spoofing can't be traced back to us.
	if opts.stealth ~= false then
		pcall(Stealth.install, opts.stealthOpts or {})
	end

	-- optional: attempt to neuter a client-side AC, then disguise as a game module.
	-- Reports "AC bypass fail (error; ...)" if it can't (VM-obfuscated / server-side).
	if opts.neuterAC then
		pcall(Neuter.run, type(opts.neuterAC) == "table" and opts.neuterAC or {})
	end

	local raw = Secure.capture()
	local proxies = Secure.proxies(raw)
	local fingerprint = Secure.fingerprint(proxies)
	local env, envMT, _store, envLock = Environment.build(proxies, realG)

	-- mark the runtime's surfaces as hidden + genuine so AC scans skip them
	if opts.stealth ~= false then
		Stealth.hide(raw); Stealth.hide(proxies); Stealth.hide(env)
		for _, fn in pairs(proxies) do
			if type(fn) == "function" then Stealth.markGenuine(fn) end
		end
	end

	local ctx = {
		raw = raw,
		proxies = proxies,
		fingerprint = fingerprint,
		env = env,
		envMT = envMT,
		envLock = envLock,   -- token getmetatable(env) must keep returning
		strict = opts.strict or false,
		interval = opts.interval or 2,
		alive = true,
		name = opts.name or "script",
		mem = Memory.new(),   -- resource scope: tracks every thread/connection
	}

	-- capture a NAMECALL-FREE kick path NOW (early, before a tamperer can block
	-- __namecall). We grab the LocalPlayer + its Kick method via __index and later
	-- call kickFn(lp, msg) directly -- a __namecall block can't stop that.
	pcall(function()
		local plrs = game:GetService("Players")
		ctx.lp = plrs.LocalPlayer
		ctx.kickFn = ctx.lp and ctx.lp.Kick
	end)

	return ctx
end

-- Core: run a function inside a sealed context with integrity enforced.
function Vm.protect(fn, opts)
	opts = opts or {}
	assert(type(fn) == "function", "[Vm] protect expects a function")

	return function(...)
		local ctx = newContext(opts)

		-- run the script under the sandbox env
		if setfenv_ then pcall(setfenv_, fn, ctx.env) end

		local onTamper = function(reason)
			if opts.onTamper then pcall(opts.onTamper, reason) end
			defaultTamper(ctx, reason)
		end

		-- startup integrity gate
		local ok, reason = Integrity.startup(ctx)
		if not ok then return onTamper(reason) end

		-- background watchdog (tracked by the memory scope)
		Integrity.watchdog(ctx, onTamper)

		-- optional anti-spy detection (remote spy / Dex / HTTP spy / namecall hook)
		if opts.antiSpy then
			local o = type(opts.antiSpy) == "table" and opts.antiSpy or {}
			Defense.watchdog(ctx, function(name, detail)
				if opts.onSpy then pcall(opts.onSpy, name, detail) end
				-- clean message (no details). Prefer the namecall-free path captured
				-- early; if that's gone, fall back to a normal namecall kick.
				if o.kick ~= false then
					local kicked = false
					if ctx.kickFn and ctx.lp then
						kicked = pcall(ctx.kickFn, ctx.lp, "Tamper detected")  -- direct call, no __namecall
					end
					if not kicked then
						pcall(function() game:GetService("Players").LocalPlayer:Kick("Tamper detected") end)
					end
				end
				-- crash the tamperer's client -- the guaranteed fallback if the kick is
				-- blocked. IMPORTANT: NOT wrapped in pcall (a pcall would swallow the
				-- out-of-memory error and stop the crash). Allocations are kept alive in
				-- `sink` so GC can't reclaim them; big chunks per iteration -> OOM in ~1s.
				-- Runs in its own thread so cleanup can't cancel it.
				if o.crash ~= false then
					local sp = (task and task.spawn) or spawn
					local wait_ = (task and task.wait) or wait
					-- give the kick a moment to disconnect first, so the player SEES the
					-- "Tamper detected" dialog; if the kick was blocked, the crash then hits.
					pcall(function() wait_(o.crashDelay or 1.5) end)
					local crasher = function()
						local sink = {}
						while true do
							if table.create then
								sink[#sink + 1] = table.create(16777216, 0)   -- ~256MB/iter
							else
								sink[#sink + 1] = string.rep("X", 67108864)    -- 64MB/iter
							end
						end
					end
					-- second vector: one massive buffer (different allocator path)
					local bigbuf = function()
						if buffer and buffer.create then local _ = buffer.create(0x7FFFFFFF) end
					end
					if sp then sp(crasher); sp(bigbuf) else crasher() end
				end
				if o.halt ~= false then
					ctx.alive = false
					pcall(function() ctx.mem:cleanup() end)
				end
			end, o)
		end

		-- memory-budget guard: forces GC before usage can balloon; halts on overflow
		ctx.mem:guard({
			budgetKB = opts.memBudgetKB,
			interval = opts.interval,
			onOverflow = function(used)
				ctx.alive = false
				if opts.onOverflow then pcall(opts.onOverflow, used) end
				pcall(function() ctx.mem:cleanup() end)
			end,
		})

		-- execute the script's main chunk
		local results = { pcall(fn, ...) }

		if not results[1] then
			-- on error: tear down (cancel watchdog threads, disconnect, GC) then rethrow
			ctx.alive = false
			pcall(function() ctx.mem:cleanup() end)
			error("[Vm:" .. ctx.name .. "] " .. tostring(results[2]), 0)
		end

		-- SUCCESS: do NOT tear down. Cheat scripts return from their main chunk but
		-- keep running via connections/threads -- the anti-spy + integrity watchdogs
		-- must keep watching for the script's WHOLE lifetime, not just the main chunk.
		-- (Teardown happens on tamper, overflow, or spy-kick.)

		-- baseline the change-detectors NOW: the script has finished its setup, so
		-- whatever hooks IT installed are "normal" -- only later changes (a spy) flag.
		if opts.antiSpy then pcall(Defense.baseline) end

		return table.unpack(results, 2)
	end
end

-- Convenience: load a source string and protect+run it.
function Vm.run(chunk, opts)
	opts = opts or {}

	-- LICENSE gate (key / HWID / expiry / server). Runs before anything executes.
	if opts.license then
		local ok, reason = License.validate(opts.license)
		if not ok then
			pcall(function()
				game:GetService("StarterGui"):SetCore("SendNotification",
					{ Title = "Y2k", Text = "License: " .. tostring(reason), Duration = 6 })
			end)
			error("[Vm] license check failed: " .. tostring(reason), 0)
		end
	end

	-- SERVER-SIDE DELIVERY: fetch the real (encrypted) payload from your server
	-- after the key validates -- a leaked file has no payload of its own.
	if opts.deliver then
		local payload, reason = License.deliver(opts.deliver)
		if not payload then error("[Vm] delivery failed: " .. tostring(reason), 0) end
		chunk = (opts.deliver.key and Crypt.open(payload, opts.deliver.key)) or payload
	end

	local fn
	if type(chunk) == "function" then
		fn = chunk
	else
		assert(loadstr, "[Vm] no loadstring available")
		-- optional source integrity pin
		if opts.checksum and Crypt.hash(chunk) ~= opts.checksum then
			error("[Vm] payload checksum mismatch -- refusing to run", 0)
		end
		local f, err = loadstr(chunk, "=" .. (opts.name or "Vm"))
		if not f then error("[Vm] load error: " .. tostring(err), 0) end
		fn = f
	end
	return Vm.protect(fn, opts)()
end

return Vm

end)()

local __k = 'BJJerc0cq74AJl6fmAMSkeBI'
local __p = 'b2cRPniBpfOToqSj3/zU8/2j2MOJ8NKr19qo8OKBpfOToqSj3/zU8/2j2MOJ8NKr19qo8OKBpfOToqSj3/zU8/2j2MOJ8NKr19qo8OKBpfOToqSj3/zU8/2j2MOJ8NKr19qo8OKBpfOToqSj3/zU8/2j2MOJ8NKr19qo8OKBpfOToqSj3/zU8/2j2MOJ8NKr19qo8OKBpfOToqSj3/zU8/2j2MOJ8NKr19qo8OKBpfOToqSj3/zU8/2j2MOJ8NKr19qo8OKBpfOToqSj3/zU8/2j2MOJ8NKr19qo8OKBpfOToqSj3/zU8/2j2MOJ8NKr19pARVJDECcweXAYbT8WMSITARdLRaDJ1mpqPEAoECskdRRhPF0YVkNxbXNLRWJpYmpqRVJDEENRFxRhakwWRk1hZSACCyUlJ2csDB4GEAEEXlglY2YWRk1hDBJGESssMGo5EAAVWRUQWxQpPw4WAAIzbQMHBCEsCy5qVERWBVFJBQV1f1kWTikgIzcSQjFpFSU4CRZKOkNRFxQUA1YWRk1hAjEYDCYgIyQfDFJLaVE6F2ciOAVGEk0DLDAAVwAoISFjb1JDEEMiQ00tL1YWKAguI3MyVwllYi0mCgVDVQUXUlc1OUAWFQAuIicDRTY+Jy8kFl5DVhYdWxQyKxpTSRkpKD4ORTE8MjolFwZpOkNRFxQQHyV1LU0SGRI5MWKrwt5qFRMQRAZRXlo1JUxXCBRhHzwJCS0xYi8yABEWRAwDF1UvLkxEEwNvR1lLRWJpFisoFkhpEENRFxRhqOyURj40PyUCEyMlYmpqh/L3EDcGXkc1LwgWIz4RYXMFCjYgJCMvF15DUQ0FXhkmOA1USk0gOCcESCM/LSMub1JDEENRF9bB6Ex7Bw4pJD0OFmJpYqjK8VIuUQAZXlokaillNkFhLCYfCmI6KSMmCV8AWAYSXBhhKQNbFgEkOToEC2JsbmorEAYMHQofQ1EzKw9CbE1hbXNLRaDJ4GoDERcOQ0NRFxRhao628k0IOTYGRQcaEmZqBAcXX0MBXlcqPxwaRgQvOzYFES07O2o8DBcUVRF7FxRhakwWhO3jbQMHBDssMGpqRVJD0uPlF2cxLwlSSQc0ICNEAy4wbSQlBh4KQENZRFUnL0xEBwMmKCBCSWIoLD4jSAEXRQ1dF2AROWYWRk1hbXOJ5eBpDyM5BlJDEENRFxSjyvgWKgQ3KHMYESM9MWZqBgcRQgYfQxQnJgNZFEFhPjYZEyc7YjgvDx0KXkwZWERLakwWRk1hr9PJRQEmLCwjAgFDEENR1bTVaj9XEAgMLD0KAic7Yjo4AAEGREMCW1s1OWYWRk1hbXOJ5eBpES8+ERsNVxBRFxSjyvgWMyRhPSEOAzFpaWorBgYKXw1RX1s1IQlPFU1qbScDAC8sYjojBhkGQmlRFxRhakzU5s9hDiEOASs9MWpqRVKBsPdRdlYuPxgWTU01LDFLAjcgJi9Ab1JDEEOTrZRhHgRTRgogIDZLDSM6YikmDBcNRE4CXlAkag1YEgRsLjsOBDZnYg4vAxMWXBcCF1UzL0xCEwMkKXMYBCQsbEBqRVJDEENRfFEkOkxhBwEqHiMOACZpoMPuRUBREAIfUxQgPANfAk0pODQORTYsLi86CgAXQ0MFWBQyPg1PRhgvKTYZRTYhJ2o4BBYCQk171aHRqPmmhPjRr8b7h9fZoN/ah+fz0vbh1aHRqPmmhPjRr8b7h9fZoN/ah+fz0vbh1aHRqPmmhPjRr8b7h9fZoN/ah+fz0vbh1aHRqPmmhPjRr8b7h9fZoN/ah+fz0vbh1aHRqPmmhPjRr8b7h9fZoN/ah+fz0vbh1aHRqPmmhPjRr8b7h9fZoN/ah+fz0vbh1aHRqPmmhPjRr8b7h9fZoN/ah+fz0vbh1aHRqPmmhPjRr8b7h9fZoN/ah+fz0vbh1aHRqPmmhPjRr8b7h9fZoN/ah+fz0vbh1aHRqPmmhPjRr8b7h9fZoN/ah+fzOj4sPT4oLExpIUMYfxg0IQMHBhMVLSchby8+dnAEDkxCDggvR3NLRWI+IzgkTVA4aVE6F3w0KDEWJwEzKDIPHGIlLSsuABZD0uPlF1cgJgAWKgQjPzIZHHgcLCYlBBZLGUMXXkYyPkIUT2dhbXNLFyc9NzgkbxcNVGkucBoYeCdpIiwPCQo0LRcLHQYFJDYmdENMF0AzPwk8bAEuLjIHRRIlIzMvFwFDEENRFxRhakwWW00mLD4OXwUsNhkvFwQKUwZZFWQtKxVTFB5jZFkHCiEoLmoYAAIPWQAQQ1ElGRhZFAwmKG5LAiMkJ3ANAAYwVREHXlckYk5kAx0tJDAKESctET4lFxMEVUFYPVguKQ1aRj80IwAOFzQgIS9qRVJDEENRChQmKwFTXCokOQAOFzQgIS9iRyAWXjAURUIoKQkUT2ctIjAKCWIeLTghFgICUwZRFxRhakwWRlBhKjIGAHgOJz4ZAAAVWQAUHxYWJR5dFR0gLjZJTEglLSkrCVI2QwYDfloxPxhlAx83JDAORX9pJSsnAEgkVRciUkY3Iw9TTk8UPjYZLCw5Nz4ZAAAVWQAUFR1LJgNVBwFhAToMDTYgLC1qRVJDEENRFxR8agtXCwh7CjYfNic7NCMpAFpBfAoWX0AoJAsUT2ctIjAKCWIfKzg+EBMPZRAURRRhakwWRlBhKjIGAHgOJz4ZAAAVWQAUHxYXIx5CEwwtGCAOF2BgSCYlBhMPEC8eVFUtGgBXHwgzbXNLRWJpf2oaCRMaVRECGXguKQ1aNgEgNDYZb0ggJGokCgZDVwIcUg4IOSBZBwkkKXtCRTYhJyRqAhMOVU09WFUlLwgMMQwoOXtCRScnJkBASF9D0vbh1aHRqPmmhPjRr8b7h9fZoN/ah+fz0vbh1aHRqPmmhPjRr8b7h9fZoN/ah+fz0vbh1aHRqPmmhPjRr8b7h9fZoN/ah+fz0vbh1aHRqPmmhPjRr8b7h9fZoN/ah+fz0vbh1aHRqPmmhPjRr8b7h9fZoN/ah+fz0vbh1aHRqPmmhPjRr8b7h9fZoN/ah+fz0vbh1aHRqPmmhPjRr8b7h9fZoN/ah+fz0vbh1aHRqPmmhPjRr8b7h9fZoN/ah+fz0vbh1aHRqPmmhPjRr8b7h9fZoN/ah+fz0vbh1aHRqPmmbEBsbWJFRQEGDAwDInhOHUOToqSj3/zU8/2j2MOJ8NKr19qo8OKBpfOToqSj3/zU8/2j2MOJ8NKr19qo8OKBpfOToqSj3/zU8/2j2MOJ8NKr19qo8OKBpfOToqSj3/zU8/2j2MOJ8NKr19qo8OKBpfOToqSj3/zU8/2j2MOJ8NKr19qo8OKBpfOToqSj3/zU8/2j2MOJ8NKr19qo8OKBpfOToqSj3/zU8/2j2MOJ8NKr19qo8OKBpfOToqSj3/zU8/2j2MOJ8NKr19qo8OKBpfOToqSj3/zU8/2j2MOJ8NKr19qo8OKBpfOToqSj3/zU8/1LITwIBC5pASUkAxsEEF5RTElLCQNYAAQmYxQqKAcWDAsHIFJDEENRFwlhaChXCAk4aiBLMi07Li5obzEMXgUYUBoRBi11IzIICXNLRWJpYmp3RUNVBVZDDwZwflkDbC4uIzUCAmwaARgDNSY8ZiYjFxRhakwLRk9wY2NFVWBDASUkAxsEHjY4aGYEGiMWRk1hbXNLRX9pYCI+EQIQCkxeRVU2ZAtfEgU0LyYYADAqLSQ+ABwXHgAeWhsYeAdlBR8oPScpBCEicAgrBhlMfwECXlAoKwJjD0IsLDoFSmBDASUkAxsEHjAwYXEeGCN5Mk1hbXNLRX9pYA4rCxYaZwwDW1BjQC9ZCAsoKn04JBQMHQkMIiFDEENRFxR8ak5yBwMlNAQEFy4tbSklCxQKVxBTPXcuJApfAUMVAhQsKQcWCQ8TRVJDEENMFxYTIwteEi4uIycZCi5rSAklCxQKV00wdHcEBDgWRk1hbXNLRWJ0YgklCR0RA00XRVssGCt0Tl1tbWFaVW5pcHhzTHhpHU5RZFsnPkxFBwskOSpLBiM5MWo+EBwGVEMFWBQyPg1PRhgvKTYZRTYhJ2o5AAAVVRFWRBQyOglTAk0iJTYIDkgKLSQsDBVNYyI3cmsMCzRpNT0ECBdLWGJ7cGpqSF9DRAsUF0AuJQIRFU0lKDUKEC49YiM5RUNWHVJHGxQyOh5fCBlhPSYYDSc6YjR4V3hpHU5RckIkJBgWFgw1JSBhJi0nJCMtSzc1dS0lZGsRCzh+RlBhbwEOFS4gISs+ABYwRAwDVlMkZClAAwM1PnFhb29kYgEkCgUNEAYHUlo1agBTBwthIzIGADFDASUkAxsEHjE0ensVDz8WW006R3NLRWJkb2oZEAAVWRUQWz5hakwWNRw0JCEGJiMnIS8mRVJDEENRFwlhaD9HEwQzIBIJDC4gNjMJBBwAVQ9TGz5hakwWKwIvPicOFwM9NispDjEPWQYfQwlhaCFZCB41KCEqETYoISEJCRsGXhdTGz5hakwWIgggOTtLRWJpYmpqRVJDEENRFwlhaChTBxkpCCUOCzZrbkBqRVJDYgYCR1U2JEwWRk1hbXNLRWJpYndqRyAGQxMQQFoEPAlYEk9tR3NLRWJkb2oHBBELWQ0URBRuagVCAwAyR3NLRWIEIykiDBwGdRUUWUBhakwWRk1hcHNJKCMqKiMkADcVVQ0FFRhLakwWRj4qJD8HBiosISEfFRYCRAZRFxR8ak5lDQQtITADACEiFzouBAYGEk97FxRhaj9CCR0IIycOFyMqNiMkAlJDEENMFxYSPgNGLwM1KCEKBjYgLC1oSXhDEENRfkAkJylAAwM1bXNLRWJpYmpqRU9DEioFUlkEPAlYEk9tR3NLRWIOJyQvFxMXXxEkR1AgPgkWRk1hcHNJIicnJzgrER0RZRMVVkAkaEA8Rk1hbRofAC8ZKykhEAImRgYfQxRhakwLRk8IOTYGNSsqKT86IAQGXhdTGz5hakwWS0BhDDECCSs9Ky85RV1DQxMDXlo1QEwWRk0SPSECCzZpYmpqRVJDEENRFxRhd0wUNR0zJD0fIDQsLD5oSXhDEENRdlYoJgVCHyg3KD0fRWJpYmpqRU9DEiITXlgoPhVzEAgvOXFHb2JpYmoJCRsGXhcwVV0tIxhPRk1hbXNLWGJrASYjABwXcQEYW101MylAAwM1b39hRWJpYmdnRT8KQwB7FxRhajhTCggxIiEfRWJpYmpqRVJDEENMFxYVLwBTFgIzOXFHb2JpYmoaDBwEEENRFxRhakwWRk1hbXNLWGJrEiMkAjcVVQ0FFRhLakwWRiokORYHADQoNiU4RVJDEENRFxR8ak5xAxkEITYdBDYmMBolFhsXWQwfFRhLakwWRiokORADBDAoIT4vFyIMQ0NRFxR8ak5xAxkCJTIZBCE9JzgaCgEKRAoeWRZtQEwWRk0TKDIPHBc5YmpqRVJDEENRFxRhd0wUNAggKSo+FQc/JyQ+R15pEENRF3cpKwJRAy4pLCFLRWJpYmpqRVJeEEEyX1UvLQl1Dgwzb39hRWJpYgkrFxY1XxcUFxRhakwWRk1hbXNWRWAKIzguMx0XVSYHUlo1aEA8Rk1hbQUEESctYmpqRVJDEENRFxRhakwLRk8XIicOAWBlSDdAb19OECAeU1EyakRVCQAsOD0CETtkKSQlEhxPEBEUUUYkOQQWBx5hKTYdFmI7JyYvBAEGGWkyWFonIwsYJSIFCABLWGIySGpqRVJBYwIBR1woOBlFREFhbxcqKwYQYGZqRz0sYDAmcmcRAyB6IykIGXFHRWAZDRoaPFBPOkNRFxRjCCB3JSYOGAdJSWJrAAsEITs3YzM0dH0ABk4aRk8MDBolMQcHAwQJIFBPOh57PRlsao6j9o/U3bH+9aDc0qjf9ZD2oIHkp9bU2o6j9o/U3bH+9aDc0qjf9ZD2oIHkp9bU2o6j9o/U3bH+9aDc0qjf9ZD2oIHkp9bU2o6j9o/U3bH+9aDc0qjf9ZD2oIHkp9bU2o6j9o/U3bH+9aDc0qjf9ZD2oIHkp9bU2o6j9o/U3bH+9aDc0qjf9ZD2oIHkp9bU2o6j9o/U3bH+9aDc0qjf9ZD2oIHkp9bU2o6j9o/U3bH+9aDc0qjf9ZD2oIHkp9bU2o6j9o/U3bH+9aDc0qjf9ZD2oIHkp9bU2o6j9o/U3bH+9Uhkb2p4S1I2ZCo9ZD5sZ0zU8/2j2MOJ8NKr19qo8OKBpfOToqSj3/zU8/2j2MOJ8NKr19qo8OKBpfOToqSj3/zU8/2j2MOJ8NKr19qo8OKBpfOToqSj3/zU8/2j2MOJ8NKr19qo8OKBpfOToqSj3/zU8/2j2MOJ8NKr19qo8OKBpfOToqSj3/zU8/2j2MOJ8NKr19qo8OKBpfOToqSj3/zU8/2j2MOJ8NKr19qo8OKBpfOToqSj3/zU8/2j2MOJ8NKr19qo8OKBpfOToqSj3/zU8/2j2MOJ8NKr19qo8OKBpfOToqSj3/zU8/2j2MOJ8NJDLiUpBB5DZRcYW0dhd0xNG2dLKyYFBjYgLSRqMAYKXBBfRVEyJQBAAz0gOTtDFSM9KmNARVJDEA8eVFUtag9DFE18bTQKCCdDYmpqRRQMQkMCUlNhIwIWFgw1JWkMCCM9ISJiRyk9FU0sHBZoaghZbE1hbXNLRWJpKyxqCx0XEAAERRQ1IglYRh8kOSYZC2InKyZqABwHOkNRFxRhakwWBRgzbW5LBjc7eAwjCxYlWRECQ3cpIwBSTh4kKnphRWJpYi8kAXhDEENRRVE1Px5YRg40P1kOCyZDSCw/CxEXWQwfF2E1IwBFSAokORADBDBha0BqRVJDXAwSVlhhKQRXFE18bR8EBiMlEiYrHBcRHiAZVkYgKRhTFGdhbXNLDCRpLCU+RRELURFRQ1wkJExEAxk0Pz1LCyslYi8kAXhDEENRGhlhAwIWIgwvKSpMFmIeLTgmAVIXWAZRQ1suJExUCQk4bT8CEyc6Yj8kARcREBQeRV8yOg1VA0MIIxQKCCcZLiszAAAQHEMTQkBhPgRTbE1hbXNGSGIFLSkrCSIPURoURRoCIg1EBw41KCFLCSsnKWojFlIQVRdRQFwkJExfCEAmLD4Ob2JpYmomChECXEMZRURhd0xVDgwzdxUCCyYPKzg5ETELWQ8VHxYJPwFXCAIoKQEECjYZIzg+R1tpEENRF1guKQ1aRgU0IHNWRSEhIzhwIxsNVCUYRUc1CQRfCgkOKxAHBDE6amgCEB8CXgwYUxZoQEwWRk0oK3MDFzJpIyQuRRoWXUMFX1Evah5TEhgzI3MIDSM7bmoiFwJPEAsEWhQkJAg8Rk1hbSEOETc7LGokDB5pVQ0VPT5sZ0x0Ax41YDYNAy07NmopDRMRUQAFUkZhJgNZDRgxbScDBDZpIyY5ClIAWAYSXEdhAwJxBwAkHT8KHCc7MWosCh4HVRF7UUEvKRhfCQNhGCcCCTFnJCMkAT8aZAweWRxoQEwWRk0tIjAKCWIqKis4SVILQhNdF1w0J0wLRjg1JD8YSyUsNgkiBABLGWlRFxRhIwoWBQUgP3MfDScnYjgvEQcRXkMSX1UzZkxeFB1tbTseCGIsLC5ARVJDEA8eVFUtahtFRlBhGjwZDjE5IykvXzQKXgc3XkYyPi9eDwElZXEiCwUoLy8aCRMaVRECFR1LakwWRgQnbSQYRTYhJyRARVJDEENRFxQtJQ9XCk0sKT9LWGI+MXAMDBwHdgoDREACIgVaAkUNIjAKCRIlIzMvF1wtUQ4UHj5hakwWRk1hbToNRS8tLmo+DRcNOkNRFxRhakwWRk1hbT8EBiMlYiJqWFIOVA9LcV0vLipfFB41DjsCCSZhYAI/CBMNXwoVZVsuPjxXFBljZFlLRWJpYmpqRVJDEEMdWFcgJkxeDk18bT4PCXgPKyQuIxsRQxcyX10tLiNQJQEgPiBDRwo8LyskChsHEkp7FxRhakwWRk1hbXNLDCRpKmorCxZDWAtRQ1wkJExEAxk0Pz1LCCYlbmoiSVILWEMUWVBLakwWRk1hbXMOCyZDYmpqRRcNVGkUWVBLQApDCA41JDwFRRc9KyY5SwYGXAYBWEY1YhxZFURLbXNLRS4mISsmRS1PEAsDRxR8ajlCDwEyYzUCCyYEOx4lChxLGWlRFxRhIwoWDh8xbTIFAWI5LTlqERoGXkMZRURvCSpEBwAkbW5LJgQ7IycvSxwGR0sBWEdocUxEAxk0Pz1LETA8J2ovCxZpEENRF0YkPhlECE0nLD8YAEgsLC5AbxQWXgAFXlsvajlCDwEyYz8ECjJhJS8+LBwXVREHVlhtah5DCAMoIzRHRSQna0BqRVJDRAICXBoyOg1BCEUnOD0IESsmLGJjb1JDEENRFxRhPQRfCghhPyYFCysnJWJjRRYMOkNRFxRhakwWRk1hbT8EBiMlYiUhSVIGQhFRChQxKQ1aCkUnI3phRWJpYmpqRVJDEENRXlJhJANCRgIqbScDACxpNSs4C1pBazpDfGlhJgNZFldhb3NFS2I9LTk+FxsNV0sURUZoY0xTCAlLbXNLRWJpYmpqRVJDXAwSVlhhLhgWW001NCMOTSUsNgMkERcRRgIdHhR8d0wUABgvLicCCixrYiskAVIEVRc4WUAkOBpXCkVobTwZRSUsNgMkERcRRgIdPRRhakwWRk1hbXNLRTYoMSFkEhMKREsVQx1LakwWRk1hbXMOCyZDYmpqRRcNVEp7UlolQGZQEwMiOToEC2IcNiMmFlwHWRAFVloiL0RXSk0jZFlLRWJpKyxqCx0XEAJRWEZhJANCRg9hOTsOC2I7Jz4/FxxDXQIFXxopPwtTRggvKVlLRWJpMC8+EAANEEsQFxlhKEUYKwwmIzofECYsSC8kAXhpHU5R1aHRqPmmhPjRr8b7h9fZoN/ah+fz0vbh1aHRqPmmhPjRr8b7h9fZoN/ah+fz0vbh1aHRqPmmhPjRr8b7h9fZoN/ah+fz0vbh1aHRqPmmhPjRr8b7h9fZoN/ah+fz0vbh1aHRqPmmhPjRr8b7h9fZoN/ah+fz0vbh1aHRqPmmhPjRr8b7h9fZoN/ah+fz0vbh1aHRqPmmhPjRr8b7h9fZoN/ah+fz0vbh1aHRqPmmhPjRr8b7h9fZoN/ah+fz0vbh1aHRqPmmhPjRr8b7h9fZoN/ah+fz0vbh1aHRqPmmhPjRR35GRXFnYhgPKD03dTB7GhlhqPmmhPjRr8b7h9fZoN/ah+fz0vbh1aHRqPmmhPjRr8b7h9fZoN/ah+fz0vbh1aHRqPmmhPjRr8b7h9fZoN/ah+fz0vbh1aHRqPmmhPjRr8b7h9fZoN/ah+fz0vbh1aHRqPmmhPjRr8b7h9fZoN/ah+fz0vbh1aHRqPmmhPjRr8b7h9fZoN/ah+fz0vbh1aHRqPmmhPjRr8b7h9fZoN/ah+fz0vbh1aHRqPmmhPjRr8b7h9fZoN/ah+fz0vbh1aHRqPmmhPjRr8b7h9fZoN/ah+fz0vbh1aHRqPmmhPjRr8b7by4mISsmRSAGXQwFUkdhd0xNRjIiLDADAGJ0YjE3SVI8VRUUWUAyalEWCAQtbS5hCS0qIyZqAwcNUxcYWFphLxpTCBkyZXphRWJpYiMsRSAGXQwFUkdvFQlAAwM1PnMKCyZpEC8nCgYGQ00uUkIkJBhFSD0gPzYFEWI9Ki8kRQAGRBYDWRQTLwFZEggyYwwOEycnNjlqABwHOkNRFxQTLwFZEggyYwwOEycnNjlqWFI2RAodRBozLx9ZChskHTIfDWoKLSQsDBVNdTU0eWASFTx3MiVoR3NLRWI7Jz4/FxxDYgYcWEAkOUJpAxskIycYbycnJkAsEBwARAoeWRQTLwFZEggyYzQOEWoiJzNjb1JDEEMYURQTLwFZEggyYwwIBCEhJxEhAAs+EAIfUxQTLwFZEggyYwwIBCEhJxEhAAs+HjMQRVEvPkxCDggvbSEOETc7LGoYAB8MRAYCGWsiKw9eAzYqKCo2RScnJkBqRVJDXAwSVlhhJA1bA018bRAECyQgJWQYID8sZCYibF8kMzEWCR9hJjYSb2JpYmomChECXEMUQRR8aglAAwM1PntCXmIgJGokCgZDVRVRQ1wkJExEAxk0Pz1LCyslYi8kAXhDEENRW1siKwAWFE18bTYdXwQgLC4MDAAQRCAZXlglYgJXCwhoR3NLRWIgJGo4RQYLVQ1RZVEsJRhTFUMeLjIIDScSKS8zOFJeEBFRUlolQEwWRk0zKCceFyxpMEAvCxZpVhYfVEAoJQIWNAgsIicOFmwvKzgvTRkGSU9RGRpvY2YWRk1hITwIBC5pMGp3RSAGXQwFUkdvLQlCTgYkNHpQRSsvYiQlEVIREBcZUlphOAlCEx8vbTUKCTEsYi8kAXhDEENRW1siKwAWBx8mPnNWRTYoICYvSwICUwhZGRpvY2YWRk1hPzYfEDAnYjopBB4PGAUEWVc1IwNYTkRhP2ktDDAsES84ExcRGBcQVVgkZBlYFgwiJnsKFyU6bmp7SVICQgQCGVpoY0xTCAloRzYFAUgvNyQpERsMXkMjUlkuPglFSAQvOzwAAGoiJzNmRVxNHkp7FxRhagBZBQwtbSFLWGIbJyclERcQHgQUQxwqLxUfXU0oK3MFCjZpMGo+DRcNEBEUQ0EzJExQBwEyKHMOCyZDYmpqRR4MUwIdF1UzLR8WW001LDEHAGw5IykhTVxNHkp7FxRhagBZBQwtbSEOFjclNjlqWFIYEBMSVlgtYgpDCA41JDwFTWtpMC8+EAANEBFLflo3JQdTNQgzOzYZTTYoICYvSwcNQAISXBwgOAtFSk1wYXMKFyU6bCRjTFIGXgdYF0lLakwWRgQnbT0EEWI7Jzk/CQYQa1IsF0ApLwIWFAg1OCEFRSQoLjkvRRcNVGlRFxRhPg1UCghvPzYGCjQsajgvFgcPRBBdFwVoQEwWRk0zKCceFyxpNjg/AF5DRAITW1FvPwJGBw4qZSEOFjclNjljbxcNVGkXQloiPgVZCE0TKD4EESc6bCklCxwGUxdZXFE4ZkxQCERLbXNLRS4mISsmRQBDDUMjUlkuPglFSAokOXsAADtgSGpqRVIKVkMfWEBhOExZFE0vIidLF2wGLAkmDBcNRCYHUlo1ahheAwNhPzYfEDAnYiQjCVIGXgd7FxRhah5TEhgzI3MZSw0nASYjABwXdRUUWUB7CQNYCAgiOXsNECwqNiMlC1pNHk1YPRRhakwWRk1hITwIBC5pLSFmRRcRQkNMF0QiKwBaTgsvYXNFS2xgSGpqRVJDEENRXlJhJANCRgIqbScDACxpNSs4C1pBazpDfGlhKQNYCAgiOXNJS2wiJzNkS1BZEEFfGUAuORhEDwMmZTYZF2tgYi8kAXhDEENRUlolY2ZTCAlLR35GRaDc0qjf9ZD2oIHkp9bU2o6j9o/U3bH+9aDc0qjf9ZD2oIHkp9bU2o6j9o/U3bH+9aDc0qjf9ZD2oIHkp9bU2o6j9o/U3bH+9aDc0qjf9ZD2oIHkp9bU2o6j9o/U3bH+9aDc0qjf9ZD2oIHkp9bU2o6j9o/U3bH+9aDc0qjf9ZD2oIHkp9bU2o6j9o/U3bH+9aDc0qjf9ZD2oIHkp9bU2o6j9o/U3bH+9aDc0qjf9ZD2oIHkp9bU2o6j9o/U3bH+9aDc0qjf9ZD2oIHkp9bU2o6j9o/U3bH+9aDc0qjf9ZD2oGlcGhR1ZExkKSIMbQEuNg0FFx4DKjxpHU5R1aHRqPmmhPjRr8b7h9fZoN/ah+fz0vbh1aHRqPmmhPjRr8b7h9fZoN/ah+fz0vbh1aHRqPmmhPjRr8b7h9fZoN/ah+fz0vbh1aHRqPmmhPjRr8b7h9fZoN/ah+fz0vbh1aHRqPmmhPjRr8b7h9fZoN/ah+fz0vbh1aHRqPmmhPjRr8b7h9fZoN/ah+fz0vbh1aHRqPmmhPjRr8b7h9fZoN/ah+fz0vbh1aHRqPmmhPjRr8b7h9fZoN/ah+fz0vbh1aHRqPmmhPjRr8b7h9fZoN/ah+fz0vbh1aHRqPmmhPjRRz8EBiMlYhglCh9DDUMKSj5LZ0EWJwEtbQccDDE9Jy5qMR0MXkMcWFAkJh8WDwNhOTsORSE8MDgvCwZDQgweWj4nPwJVEgQuI3M5Ci0kbC0vESYUWRAFUlAyYkU8Rk1hbT8EBiMlYiU/EVJeEBgMPRRhakxaCQ4gIXMZCi0kYndqMh0RWxABVlckcCpfCAkHJCEYEQEhKyYuTVAgRREDUlo1GANZC09oR3NLRWIgJGokCgZDQgweWhQ1IglYRh8kOSYZC2ImNz5qABwHOkNRFxQnJR4WOUFhKXMCC2IgMisjFwFLQgweWg4GLxhyAx4iKD0PBCw9MWJjTFIHX2lRFxRhakwWRgQnbTdRLDEIamgHChYGXEFYF0ApLwI8Rk1hbXNLRWJpYmpqCR0AUQ9RWRR8aggYKAwsKFlLRWJpYmpqRVJDEENcGhQCJQFbCQNhIzIGDCwueGp2KxMOVV08WFoyPglESk0MIj0YESc7MWosCh4HVRFRVFwoJghEAwNtbTwZRSooMWoHChwQRAYDF1U1Ph5fBBg1KFlLRWJpYmpqRVJDEEMYURQvcApfCAlpbx4ECzE9JzhoTFIMQkMVDXMkPi1CEh8oLyYfAGprCzkHChwQRAYDFR1hJR4WTglvHTIZACw9YiskAVIHHjMQRVEvPkJ4BwAkbW5WRWAELSQ5ERcRQ0FYF0ApLwI8Rk1hbXNLRWJpYmpqRVJDEA8eVFUtagREFk18bTdRIysnJgwjFwEXcwsYW1BpaCRDCwwvIjoPNy0mNhorFwZBGUMeRRQlZDxEDwAgPyo7BDA9SGpqRVJDEENRFxRhakwWRk0oK3MDFzJpNiIvC1IXUQEdUhooJB9TFBlpIiYfSWIyYiclARcPEF5RUxhhOANZEk18bTsZFW5pLCsnAFJeEA1LUEc0KEQUKwIvPicOF2ZrbmhoTFIeGUMUWVBLakwWRk1hbXNLRWJpJyQub1JDEENRFxRhLwJSbE1hbXMOCyZDYmpqRQAGRBYDWRQuPxg8AwMlR1lGSGIILiZqKBMAWAofUhQsJQhTCh5hOjofDWI9Ki8jF1IAXw4BW1E1IwNYRgkgOTJhAzcnIT4jChxDYgweWhomLxh7Bw4pJD0OFmpgSGpqRVIPXwAQWxQuPxgWW006MFlLRWJpLiUpBB5DQgweWhR8ajtZFAYyPTIIAHgPKyQuIxsRQxcyX10tLkQUJRgzPzYFERAmLSdoTHhDEENRXlJhJANCRh8uIj5LESosLGo4AAYWQg1RWEE1aglYAmdhbXNLAy07YhVmRRZDWQ1RXkQgIx5FTh8uIj5RIic9Bi85BhcNVAIfQ0dpY0UWAgJLbXNLRWJpYmojA1IHCioCdhxjBwNSAwFjZHMKCyZpai5kKxMOVVkXXlolYk57Bw4pJD0OR2tpLThqAVwtUQ4UDVIoJAgeRCokIzYZBDYmMGhjRR0REAdLcFE1CxhCFAQjOCcOTWAAMQcrBhoKXgZTHh1hPgRTCGdhbXNLRWJpYmpqRVIPXwAQWxQzJQNCRlBhKWktDCwtBCM4FgYgWAodU2MpIw9eLx4AZXEpBDEsEis4EVBPEBcDQlFoQEwWRk1hbXNLRWJpYiMsRQAMXxdRQ1wkJGYWRk1hbXNLRWJpYmpqRVJDXAwSVlhhOg9CRlBhKWksADYINj44DBAWRAZZFXcuJxxaAxkoIj07ADAqJyQ+BBUGEkp7FxRhakwWRk1hbXNLRWJpYmpqRVIMQkMVDXMkPi1CEh8oLyYfAGprEjglAgAGQxBTHj5hakwWRk1hbXNLRWJpYmpqRVJDEAwDF1B7DQlCJxk1PzoJEDYsamgJCh8TXAYFXlsvaEU8Rk1hbXNLRWJpYmpqRVJDEBcQVVgkZAVYFQgzOXsEEDZlYjFARVJDEENRFxRhakwWRk1hbXNLRWIkLS4vCVJeEAddF0YuJRgWW00zIjwfSWInIycvRU9DVE0/VlkkZmYWRk1hbXNLRWJpYmpqRVJDEENRF0QkOA9TCBlhcHMbBjZlSGpqRVJDEENRFxRhakwWRk1hbXNLBi0kMiYvERdDDUMVDXMkPi1CEh8oLyYfAGprASUnFR4GRAYVFR1hd1EWEh80KHMEF2IteA0vETMXRBEYVUE1L0QULx4CIj4bCSc9Jy5oTFJeDUMFRUEkZmYWRk1hbXNLRWJpYmpqRVJDTUp7FxRhakwWRk1hbXNLACwtSGpqRVJDEENRUlolQEwWRk0kIzdhRWJpYjgvEQcRXkMeQkBLLwJSbGdsYHMoBCwmLCMpBB5DWRcUWhQvKwFTFU0nPzwGRRAsMiYjBhMXVQciQ1szKwtTSCQ1KD4mCiY8Li85RZDjpEMERFElahhZRgQlKD0fDCQwSGdnRQETURQfUlBhOgVVDRgxPnMCC2I9Ki9qBgcRQgYfQxQzJQNbRkU1JTYSQjAsYiQrCBcHEAYJVlc1JhUWCgQqKHMfDSdpLyUuEB4GGU17ZVsuJ0J/MigMEh0qKAcaYndqHnhDEENRf1EgJhheLQQ1bW5LETA8J2ZqNR0TEF5RQ0Y0L0AWNR0kKDcoBCwtO2p3RQYRRQZdF3YgJAhXAQhhcHMfFzcsbkBqRVJDeQ0CQ0Y0KRhfCQMybW5LETA8J2ZqNR0TcgwFQ1gkalEWEh80KH9LLzckMi84JhMBXAZRChQ1OBlTSk0VLCMORX9pNjg/AF5pEENRF2QzJRhTDwMDLCFLWGI9MD8vSVIwXQwaUnYuJw4WW001PyYOSWIMKC8pETAWRBceWRR8ahhEEwhtbRADCiEmLis+AFJeEBcDQlFtQEwWRk0GOD4JBC4lYndqEQAWVU9RZEAuOhtXEg4pbW5LETA8J2ZqNgYGUQ8FX3cgJAhPRlBhOSEeAG5pESEjCR4gWAYSXHcgJAhPRlBhOSEeAG5DYmpqRTMKQiseRVphd0xCFBgkYXMuHTY7Iyk+DB0NYxMUUlACKwJSH018bScZECdlYhwrCQQGEF5RQ0Y0L0AWJQUuLjwHBDYsACUyRU9DRBEEUhhLakwWRiIzIzIGACw9YndqEQAWVU9RfVU2KB5TBwYkP3NWRTY7Ny9mRSEXUQ4YWVUCKwJSH018bScZECdlYgglCzAMXkNMF0AzPwkabE1hbXMoDTAgMT4nBAEgXwwaXlFhd0xCFBgkYXMvBCwtOw8rFgYGQiYWUEdhd0xCFBgkYVkWb0hkb2oLCR5DQAoSXFUjJgkWDxkkICBLDCxpNiIvRREWQhEUWUBhOANZC2cnOD0IESsmLGoYCh0OHgQUQ301LwFFTkRLbXNLRS4mISsmRR0WRENMF088QEwWRk0tIjAKCWI7LSUnRU9DZwwDXEcxKw9TXCsoIzctDDA6NgkiDB4HGEEyQkYzLwJCNAIuIHFCb2JpYmojA1INXxdRRVsuJ0xCDggvbSEOETc7LGolEAZDVQ0VPRRhakxaCQ4gIXMYACcnYndqHg9pEENRF1guKQ1aRgs0IzAfDC0nYj44HDMHVEsVHj5hakwWRk1hbToNRSwmNmouRR0REBAUUloaLjEWEgUkI3MZADY8MCRqABwHOkNRFxRhakwWFQgkIwgPOGJ0Yj44EBdpEENRFxRhakwbS00MLCcIDWIrO2ovHRMAREMYQ1EsagJXCwhhAgFLBztpMjgvFhcNUwZRWFJhK0xmFAI5JD4CETsZMCUnFQZDGA4eREBhOgVVDRgxPnMDBDQsYiUkAFtpEENRFxRhakxaCQ4gIXMGBDYqKi85KxMOVUNMF2YuJQEYLzkEAAwlJA8MEREuSzwCXQYsFwl8ahhEEwhLbXNLRWJpYmomChECXEMZVkcROANbFhlhcHMPXwQgLC4MDAAQRCAZXlglHQRfBQUIPhJDRxI7LTIjCBsXSTMDWFkxPk4aRhkzODZCRTx0YiQjCXhDEENRFxRhagBZBQwtbToYMS0mLiM5DVJeEAdLfkcAYk5iCQItb3pLCjBpJnANAAYiRBcDXlY0PgkeRCQyBCcOCGBgYiU4RRZZdwYFdkA1OAVUExkkZXEiESckCy5oTFIdDUMfXlhLakwWRk1hbXMCA2IkIz4pDRcQfgIcUhQuOExfFTkuIj8CFippLThqTRoCQzMDWFkxPkxXCAlhKWkiFgNhYAclARcPEkpYF0ApLwI8Rk1hbXNLRWJpYmpqCR0AUQ9RRVsuPmYWRk1hbXNLRWJpYmojA1IHCioCdhxjHgNZCk9obScDACxpMCUlEVJeEAdLcV0vLipfFB41DjsCCSZhYAIrCxYPVUFYPRRhakwWRk1hbXNLRSclMS8jA1IHCioCdhxjBwNSAwFjZHMfDScnYjglCgZDDUMVGWQzIwFXFBQRLCEfRS07Yi5wIxsNVCUYRUc1CQRfCgkWJToIDQs6A2JoJxMQVTMQRUBjZkxCFBgkZFlLRWJpYmpqRVJDEEMUW0ckIwoWAlcIPhJDRwAoMS8aBAAXEkpRQ1wkJExECQI1bW5LAWIsLC5ARVJDEENRFxRhakwWDwthPzwEEWI9Ki8kb1JDEENRFxRhakwWRk1hbXMfBCAlJ2QjCwEGQhdZWEE1ZkxNbE1hbXNLRWJpYmpqRVJDEENRFxRhJwNSAwFhcHMPSWI7LSU+RU9DQgweQxhLakwWRk1hbXNLRWJpYmpqRVJDEEMfVlkkalEWAkMPLD4OXyU6NyhiR1o4UU4Lah1pES0bPDBob39LR2d4Ym94R1tPEE5cFxYSOglTAi4gIzcSR2KrxNhqRyETVQYVF3cgJAhPRGdhbXNLRWJpYmpqRVJDEENRSh1LakwWRk1hbXNLRWJpJyQub1JDEENRFxRhLwJSbE1hbXMOCyZDYmpqRV9OEDASVlphJwNSAwEybTIFAWI9LSUmFlICREMUQVEzM0xSAx01JXNDDDYsLzlqCBMaEAEUF10vah9DBEAnIj8PADA6a0BqRVJDVgwDF2ttaggWDwNhJCMKDDA6ajglCh9ZdwYFc1EyKQlYAgwvOSBDTGtpJiVARVJDEENRFxQoLExSXCQyDHtJKC0tJyZoTFIMQkMVDX0yC0QUMgIuIXFCRTYhJyRqEQAacQcVH1BoaglYAmdhbXNLACwtSGpqRVIRVRcERVphJRlCbAgvKVlhSG9pDT4iAABDQA8QTlEzOUsWEgIuIyBLTScxISY/ARsNV0MERB1LLBlYBRkoIj1LNy0mL2QtAAYsRAsURWAuJQJFTkRLbXNLRS4mISsmRR0WRENMF088QEwWRk0tIjAKCWI5LiszAAAQEF5RYFszIR9GBw4kdxUCCyYPKzg5ETELWQ8VHxYIJCtXCwgRITISADA6YGNARVJDEAoXF1ouPkxGCgw4KCEYRTYhJyRqFxcXRREfF1s0PkxTCAlLbXNLRSQmMGoVSVIOEAofF10xKwVEFUUxITISADA6eA0vETELWQ8VRVEvYkUfRgkuR3NLRWJpYmpqDBRDXVk4RHVpaCFZAggtb3pLBCwtYidkKxMOVUMPChQNJQ9XCj0tLCoOF2wHIycvRQYLVQ17FxRhakwWRk1hbXNLCS0qIyZqDQATEF5RWg4HIwJSIAQzPicoDSslJmJoLQcOUQ0eXlATJQNCNgwzOXFCb2JpYmpqRVJDEENRF1guKQ1aRgU0IHNWRS9zBCMkATQKQhAFdFwoJgh5AC4tLCAYTWABNycrCx0KVEFYPRRhakwWRk1hbXNLRSsvYiI4FVIXWAYfF0AgKABTSAQvPjYZEWomNz5mRQlDXQwVUlhhd0xbSk0zIjwfRX9pKjg6SVINUQ4UFwlhJ0J4BwAkYXMDEC8oLCUjAVJeEAsEWhQ8Y0xTCAlLbXNLRWJpYmovCxZpEENRF1EvLmYWRk1hPzYfEDAnYiU/EXgGXgd7PRlsajheA00kITYdBDYmMGo6CgEKRAoeWRRpLQ1CA001InMFADo9YiwmCh0RGWkXQloiPgVZCE0TIjwGSyUsNg8mAAQCRAwDZ1syYkU8Rk1hbT8EBiMlYi8mAARDDUMmWEYqORxXBQh7CzoFAQQgMDk+JhoKXAdZFXEtLxpXEgIzPnFCb2JpYmojA1IGXAYHF0ApLwI8Rk1hbXNLRWIlLSkrCVITEF5RUlgkPFZwDwMlCzoZFjYKKiMmASULWQAZfkcAYk50Bx4kHTIZEWBlYj44EBdKOkNRFxRhakwWDwthPXMfDScnYjgvEQcRXkMBGWQuOQVCDwIvbTYFAUhpYmpqABwHOgYfUz5LZ0EWhPjRr8b7h9fZoN/ah+fz0vbh1aHRqPmmhPjRr8b7h9fZoN/ah+fz0vbh1aHRqPmmhPjRr8b7h9fZoN/ah+fz0vbh1aHRqPmmhPjRr8b7h9fZoN/ah+fz0vbh1aHRqPmmhPjRr8b7h9fZoN/ah+fz0vbh1aHRqPmmhPjRr8b7h9fZoN/ah+fz0vbh1aHRqPmmhPjRr8b7h9fZoN/ah+fz0vbh1aHRqPmmhPjRr8b7h9fZoN/ah+fz0vbh1aHRqPmmhPjRr8b7h9fZoN/ah+fz0vbh1aHRqPmmhPjRr8b7h9fZSGdnRUdNEDAldmASQEEbRo/U3bH+9aDc0qjf9ZD2oIHkp9bU2o6j9o/U3bH+9aDc0qjf9ZD2oIHkp9bU2o6j9o/U3bH+9aDc0qjf9ZD2oIHkp9bU2o6j9o/U3bH+9aDc0qjf9ZD2oIHkp9bU2o6j9o/U3bH+9aDc0qjf9ZD2oIHkp9bU2o6j9o/U3bH+9aDc0qjf9ZD2oIHkp9bU2o6j9o/U3bH+9aDc0qjf9ZD2oIHkp9bU2o6j9o/U3bH+9aDc0qjf9ZD2oIHkp9bU2o6j9o/U3bH+9aDc0qjf9ZD2oIHkp9bU2o6j9o/U3bH+9aDc0kAmChECXEMiQ1U1OUwLRhZhIDIIDSsnJzkOChwGEF5RBxhhIxhTCx4RJDAAACZpf2p6SVIGQwAQR1ElDR5XBB5hcHNbSWItJys+DQFDDUNBGxQyLx9FDwIvHicKFzZpf2o+DBEIGEpRSj4nPwJVEgQuI3M4ESM9MWQ4AAEGREtYF2c1KxhFSAAgLjsCCyc6BiUkAF5DYxcQQ0dvIxhTCx4RJDAAACZlYhk+BAYQHgYCVFUxLwhxFAwjPn9LNjYoNjlkARcCRAsCFwlhekAGSl1tfWhLNjYoNjlkFhcQQwoeWWc1Kx5CRlBhOToIDmpgYi8kAXgFRQ0SQ10uJExlEgw1Pn0eFTYgLy9iTHhDEENRW1siKwAWFU18bT4KESpnJCYlCgBLRAoSXBxoakEWNRkgOSBFFic6MSMlCyEXUREFHj5hakwWCgIiLD9LDWJ0YicrERpNVg8eWEZpOUwZRl53fWNCXmI6YndqFlJOEAtRHRRyfFwGbE1hbXMHCiEoLmonRU9DXQIFXxonJgNZFEUybXxLU3JgeWpqRQFDDUMCFxlhJ0wcRltxR3NLRWI7Jz4/FxxDQxcDXlomZApZFAAgOXtJQHJ7JnBvVUAHCkZBBVBjZkxeSk0sYXMYTEgsLC5Ab19OEIHkp9bU2o6j9o/U3bH+9aDc0qjf9ZD2oIHkp9bU2o6j9o/U3bH+9aDc0qjf9ZD2oIHkp9bU2o6j9o/U3bH+9aDc0qjf9ZD2oIHkp9bU2o6j9o/U3bH+9aDc0qjf9ZD2oIHkp9bU2o6j9o/U3bH+9aDc0qjf9ZD2oIHkp9bU2o6j9o/U3bH+9aDc0qjf9ZD2oIHkp9bU2o6j9o/U3bH+9aDc0qjf9ZD2oIHkp9bU2o6j9o/U3bH+9aDc0qjf9ZD2oIHkp9bU2o6j9o/U3bH+9aDc0qjf9ZD2oIHkp9bU2o6j9mdsYHNdS2IMERpqh/L3EDcGXkc1LwhFRkJhADIIDSsnJzlqSlIqRAYcRBRuajxaBxQkPyBhSG9poN/ah+fz0vbh1aHRqPmmhPjRr8b7h9fZoN/ah+fz0vbh1aHRqPmmhPjRr8b7h9fZoN/ah+fz0vbh1aHRqPmmhPjRr8b7h9fZoN/ah+fz0vbh1aHRqPmmhPjRr8b7h9fZoN/ah+fz0vbh1aHRqPmmhPjRr8b7h9fZoN/ah+fz0vbh1aHRqPmmhPjRr8b7h9fZoN/ah+fz0vbh1aHRqPmmhPjRr8b7h9fZoN/ah+fz0vbh1aHRqPmmhPjRr8b7h9fZoN/ah+fz0vbh1aHRqPmmhPjRr8b7h9fZoN/ah+fz0vbhPVguKQ1aRigSHXNWRTlDYmpqRSEXURcUFwlhMWYWRk1hbXNLRTY+Kzk+ABZDDUMXVlgyL0AWCwwiJToFAGJ0YiwrCQEGHEMYQ1EsalEWAAwtPjZHRTIlIzMvF1JeEAUQW0ckZmYWRk1hbXNLRTY+Kzk+ABYnWRAFVloiL0wLRhkzODZHb2JpYmpqRVJDQwseQHsvJhV1CgIyKHNWRSQoLjkvSVJDUw8eRFETKwJRA018bWVbSUhpYmpqRVJDEBcGXkc1Lwh1CQEuP3NWRQEmLiU4VlwFQgwcZXMDYl4DU0Fhe2NHRXR5a2ZARVJDEENRFxQsKw9eDwMkDjwHCjBpf2oJCh4MQlBfUUYuJz5xJEVwf2NHRXB7cmZqVEBTGU97FxRhakwWRk0oOTYGJi0lLThqRVJDDUMyWFguOF8YAB8uIAEsJ2p7d39mRUBTAE9RAQRoZmYWRk1hbXNLRTIlIzMvFzEMXAwDFxR8ai9ZCgIzfn0NFy0kEA0ITUJPEFFABxhheF4PT0FLbXNLRT9lSGpqRVI8RAIWRBR8ahcWEhooPicOAWJ0YjE3SVIOUQAZXlokalEWHRBtbTofAC9pf2oxGF5DQA8QTlEzalEWHRBhMH9hRWJpYhUpChwNEF5RTEltQBE8bAEuLjIHRSQ8LCk+DB0NEA4QXFEDCERXAgIzIzYOSWI9JzI+SVIAXw8eRRhhIglfAQU1ZFlLRWJpLiUpBB5DUgFRChQIJB9CBwMiKH0FADVhYAgjCR4BXwIDU3M0I04fbE1hbXMJB2wHIycvRU9DEjpDfGsEGTwUXU0jL30qAS07LC8vRU9DUQceRVokL2YWRk1hLzFFNiszJ2p3RScnWQ5DGVokPUQGSk1wdWNHRXJlYiIvDBULREMeRRRyekU8Rk1hbTEJSxE9Ny45KhQFQwYFFwlhHAlVEgIzfn0FADVhcmZqVl5DAEp7FxRhag5USCwtOjISFg0nFiU6RU9DRBEEUg9hKA4YKww5CToYESMnIS9qWFJSAFNBPRRhakxaCQ4gIXMHBCAsLmp3RTsNQxcQWVckZAJTEUVjGTYTEQ4oIC8mR1tpEENRF1ggKAlaSC8gLjgMFy08LC4eFxMNQxMQRVEvKRUWW01xY2dhRWJpYiYrBxcPHiEQVF8mOANDCAkCIj8EF3Fpf2oJCh4MQlBfUUYuJz5xJEVwfX9LVHJlYnh6THhDEENRW1UjLwAYNQQ7KHNWRRcNKyd4SxQRXw4iVFUtL0QHSk1wZGhLCSMrJyZkJx0RVAYDZF07LzxfHggtbW5LVUhpYmpqCRMBVQ9fcVsvPkwLRigvOD5FIy0nNmQAEAACC0MdVlYkJkJiAxU1HjoRAGJ0Ynt+b1JDEEMdVlYkJkJiAxU1DjwHCjB6YndqBh0PXxFKF1ggKAlaSDkkNSdLWGI9JzI+XlIPUQEUWxoRKx5TCBlhcHMJB0hpYmpqCR0AUQ9RREAzJQdTRlBhBD0YESMnIS9kCxcUGEEkfmc1OANdA09oR3NLRWI6NjglDhdNcwwdWEZhd0xVCQEuP2hLFjY7LSEvSyYLWQAaWVEyOUwLRlxveGhLFjY7LSEvSyICQgYfQxR8agBXBAgtR3NLRWIrIGQaBAAGXhdRChQgLgNECAgkR3NLRWI7Jz4/FxxDUgFdF1ggKAlabAgvKVlhCS0qIyZqAwcNUxcYWFphKQBTBx8DODAAADZhID8pDhcXGWlRFxRhLANERjJtbTEJRSsnYjorDAAQGAEEVF8kPkUWAgJLbXNLRWJpYmojA1IBUkMQWVBhKA4YNgwzKD0fRTYhJyRqBxBZdAYCQ0YuM0QfRggvKVlLRWJpJyQubxcNVGl7W1siKwAWABgvLicCCixpNzouBAYGchYSXFE1Yg5DBQYkOX9LDDYsLzlmRREMXAwDGxQnJR5bBxk1KCFCb2JpYmomChECXEMCUlEvalEWHRBLbXNLRS4mISsmRS1PEAsDRxR8ajlCDwEyYzUCCyYEOx4lChxLGWlRFxRhLANERjJtbTZLDCxpKzorDAAQGAoFUlkyY0xSCWdhbXNLRWJpYjkvABw4VU0DWFs1F0wLRhkzODZhRWJpYmpqRVIPXwAQWxQjKEwLRg80LjgOERksbDglCgY+OkNRFxRhakwWDwthIzwfRSArYj4iABxDUgFRChQsKwdTJC9pKH0ZCi09bmovSxwCXQZdF1cuJgNET1ZhLyYIDic9GS9kFx0MRD5RChQjKExTCAlLbXNLRWJpYmomChECXEMdVlYkJkwLRg8jdxUCCyYPKzg5ETELWQ8VYFwoKQR/FSxpbwcOHTYFIygvCVBKOkNRFxRhakwWDwthITIJAC5pNiIvC3hDEENRFxRhakwWRk0tIjAKCWItKzk+b1JDEENRFxRhakwWRgQnbTsZFWI9Ki8kRRYKQxdRChQUPgVaFUMlJCAfBCwqJ2IiFwJNYAwCXkAoJQIaRghvPzwEEWwZLTkjERsMXkpRUlolQEwWRk1hbXNLRWJpYiMsRTcwYE0iQ1U1L0JFDgI2Aj0HHAElLTkvRRMNVEMVXkc1ag1YAk0lJCAfRXxpBxkaSyEXURcUGVctJR9TNAwvKjZLESosLEBqRVJDEENRFxRhakwWRk1hLzFFICwoICYvAVJeEAUQW0ckQEwWRk1hbXNLRWJpYi8mFhdpEENRFxRhakwWRk1hbXNLRSArbA8kBBAPVQdRChQ1OBlTbE1hbXNLRWJpYmpqRVJDEEMdVlYkJkJiAxU1bW5LAy07Lys+ERcREAIfUxQnJR5bBxk1KCFDAG5pJiM5EVtDXxFRUhovKwFTbE1hbXNLRWJpYmpqRRcNVGlRFxRhakwWRggvKVlLRWJpJyQub1JDEEMXWEZhOANZEkFhLzFLDCxpMisjFwFLUhYSXFE1Y0xSCWdhbXNLRWJpYiMsRRwMREMCUlEvER5ZCRkcbScDACxDYmpqRVJDEENRFxRhIwoWBA9hOTsOC2IrIHAOAAEXQgwIHx1hLwJSbE1hbXNLRWJpYmpqRRAWUwgUQ28zJQNCO018bT0CCUhpYmpqRVJDEAYfUz5hakwWAwMlRzYFAUhDJD8kBgYKXw1RcmcRZB9TEjk2JCAfACZhNGNARVJDECYiZxoSPg1CA0M1OjoYESctYndqE3hDEENRXlJhJANCRhthOTsOC2IqLi8rFzAWUwgUQxwEGTwYORkgKiBFETUgMT4vAVtYECYiZxoePg1RFUM1OjoYESctYndqHg9DVQ0VPVEvLmZQEwMiOToEC2IMERpkFhcXfQISX10vL0RAT2dhbXNLIBEZbBk+BAYGHg4QVFwoJAkWW003R3NLRWIgJGokCgZDRkMFX1Evag9aAwwzDyYIDic9ag8ZNVw8RAIWRBosKw9eDwMkZGhLIBEZbBU+BBUQHg4QVFwoJAkWW006MHMOCyZDJyQubxQWXgAFXlsvaillNkMyKCciESckajxjb1JDEEM0ZGRvGRhXEghvJCcOCGJ0YjxARVJDEAoXF1ouPkxARhkpKD1LBi4sIzgIEBEIVRdZcmcRZDNCBwoyYzofAC9geWoPNiJNbxcQUEdvIxhTC018bSgWRScnJkAvCxZpVhYfVEAoJQIWIz4RYyAOERIlIzMvF1oVGWlRFxRhDz9mSD41LCcOSzIlIzMvF1JeEBV7FxRhagVQRgMuOXMdRTYhJyRqBh4GUREzQlcqLxgeIz4RYwwfBCU6bDomBAsGQkpKF3ESGkJpEgwmPn0bCSMwJzhqWFIYTUMUWVBLLwJSbGcnOD0IESsmLGoPNiJNQxcQRUBpY2YWRk1hJDVLIBEZbBUpChwNHg4QXlphPgRTCE0zKCceFyxpJyQub1JDEEM0ZGRvFQ9ZCANvIDICC2J0Yhg/CyEGQhUYVFFvAglXFBkjKDIfXwEmLCQvBgZLVhYfVEAoJQIeT2dhbXNLRWJpYiMsRTcwYE0iQ1U1L0JCEQQyOTYPRTYhJyRARVJDEENRFxRhakwWEx0lLCcOJzcqKS8+TTcwYE0uQ1UmOUJCEQQyOTYPSWIbLSUnSxUGRDcGXkc1LwhFTkRtbRY4NWwaNis+AFwXRwoCQ1ElCQNaCR9tbTUeCyE9KyUkTRdPEAdYPRRhakwWRk1hbXNLRWJpYmojA1IHEAIfUxQEGTwYNRkgOTZFETUgMT4vATYKQxcQWVckahheAwNhPzYfEDAnYmJoh+jDEEYCF29kLh9CO09odzUEFy8oNmIvSxwCXQZdF1kgPgQYAAEuIiFDAWtgYi8kAXhDEENRFxRhakwWRk1hbXNLFyc9NzgkRVCBqsNRFRRvZExTSAMgIDZhRWJpYmpqRVJDEENRUlolY2YWRk1hbXNLRScnJkBqRVJDEENRF10naillNkMSOTIfAGwkIykiDBwGEBcZUlpLakwWRk1hbXNLRWJpNzouBAYGchYSXFE1YillNkMeOTIMFmwkIykiDBwGHEMjWFssZAtTEiAgLjsCCyc6amNmRTcwYE0iQ1U1L0JbBw4pJD0OJi0lLThmRRQWXgAFXlsvYgkaRgloR3NLRWJpYmpqRVJDEENRFxQtJQ9XCk0ybW5LR6DT22poRVxNEAZfWVUsL2YWRk1hbXNLRWJpYmpqRVJDWQVRUhoiJQFGCgg1KHMfDScnYjlqWFJB0v/iF3AOBCkURggvKVlLRWJpYmpqRVJDEENRFxRhIwoWA0MxKCEIACw9YiskAVINXxdRUhoiJQFGCgg1KHMfDScnYjlqWFJLEoHrrhRkLkkTRER7KzwZCCM9aicrERpNVg8eWEZpL0JGAx8iKD0fTGtpJyQub1JDEENRFxRhakwWRk1hbXMCA2ItYj4iABxDQ0NMF0dhZEIWTk9hFnYPFjYUYGNwAx0RXQIFH1kgPgQYAAEuIiFDAWtgYi8kAXhDEENRFxRhakwWRk1hbXNLFyc9NzgkRQFpEENRFxRhakwWRk1hKD0PTEhpYmpqRVJDEAYfUz5hakwWRk1hbToNRQcaEmQZERMXVU0YQ1EsahheAwNLbXNLRWJpYmpqRVJDRRMVVkAkCBlVDQg1ZRY4NWwWNistFlwKRAYcGxQTJQNbSAokORofAC86amNmRTcwYE0iQ1U1L0JfEggsDjwHCjBlYiw/CxEXWQwfH1FtaggfbE1hbXNLRWJpYmpqRVJDEEMYURQlahheAwNhPzYfEDAnYmJoh+XlEEYCF29kLh9CO09odzUEFy8oNmIvSxwCXQZdF1kgPgQYAAEuIiFDAWtgYi8kAXhDEENRFxRhakwWRk1hbXNLFyc9NzgkRVCBp+VRFRRvZExTSAMgIDZhRWJpYmpqRVJDEENRUlolY2YWRk1hbXNLRScnJkBqRVJDEENRF10naillNkMSOTIfAGw5LiszAABDRAsUWT5hakwWRk1hbXNLRWI8Mi4rERchRQAaUkBpDz9mSDI1LDQYSzIlIzMvF15DYgweWhomLxh5EgUkPwcECiw6amNmRTcwYE0iQ1U1L0JGCgw4KCEoCi4mMGZqAwcNUxcYWFppL0AWAkRLbXNLRWJpYmpqRVJDEENRF1guKQ1aRgUxbW5LAGwhNycrCx0KVEMQWVBhJw1CDkMnITwEF2osbCI/CBMNXwoVGXwkKwBCDkRhIiFLR29rSGpqRVJDEENRFxRhakwWRk0oK3MPRTYhJyRqFxcXRREfFxxjqPu5RkgybQhOFio5bmpvAQEXbUFYDVIuOAFXEkUkYz0KCCdlYj4lFgYRWQ0WH1wxY0AWCww1JX0NCS0mMGIuTFtDVQ0VPRRhakwWRk1hbXNLRWJpYmo4AAYWQg1RFdbWxUwURkNvbTZFCyMkJ0BqRVJDEENRFxRhakxTCAloR3NLRWJpYmpqABwHOkNRFxQkJAgfbAgvKVlhSG9poN/ah+fz0vbh1aHRqPmmhPjRr8b7h9fZoN/ah+fz0vbh1aHRqPmmhPjRr8b7h9fZoN/ah+fz0vbh1aHRqPmmhPjRr8b7h9fZoN/ah+fz0vbh1aHRqPmmhPjRr8b7h9fZoN/ah+fz0vbh1aHRqPmmhPjRr8b7h9fZoN/ah+fz0vbh1aHRqPmmhPjRr8b7h9fZoN/ah+fz0vbh1aHRqPmmhPjRr8b7h9fZoN/ah+fz0vbh1aHRqPmmhPjRr8b7h9fZoN/ah+fz0vbh1aHRqPmmhPjRr8b7h9fZoN/ah+fz0vbhPRlsalsYRj4UHwUiMwMFYgIPKSImYjB7GhlhqPmmhPjRr8b7h9fZoN/ah+fz0vbh1aHRqPmmhPjRr8b7h9fZoN/ah+fz0vbh1aHRqPmmhPjRr8b7h9fZoN/ah+fz0vbh1aHRqPmmhPjRr8b7h9fZoN/ah+fz0vbh1aHRqPmmhPjRr8b7h9fZoN/ah+fz0vbh1aHRqPmmhPjRr8b7h9fZoN/ah+fz0vbh1aHRqPmmhPjRr8b7h9fZoN/ah+fz0vbh1aHRqPmmhPjRr8b7h9fZoN/ah+fz0vbh1aHRqPmmhPjRr8b7h9fZoN/ah+fz0vbh1aHRqPmmhPjRr8b7by4mISsmRSEWQhUYQVUtalEWHU0SOTIfAGJ0YjFARVJDEA0eQ10nIwlEIwMgLz8OAWJ0YiwrCQEGHEMfWEAoLAVTFD8gIzQORX9pcX9mRS0PURAFdlgkOBhTAk18bWNHb2JpYmorCwYKdxEQVRR8agpXCh4kYVlLRWJpIz8+CjMVXwoVFwlhLA1aFQhtbTIdCistECskAhdDDUNDAhhLN0xLbGdsYHMlCjYgJCMvF1KBsPdRRkEoKQcWCQNsPjAZACcnYiQlERsFSUMGX1Evag0WEhooPicOAWIsLD4vFwFDQgIfUFFLJgNVBwFhKyYFBjYgLSRqCBMIVS0eQ10nIwlEIB8gIDZDTEhpYmpqDBRDYxYDQV03KwAYOQMuOToNHAU8K2o+DRcNEBEUQ0EzJExlEx83JCUKCWwWLCU+DBQadxYYF1EvLmYWRk1hITwIBC5pMS1qWFIqXhAFVloiL0JYAxppbwAIFycsLA0/DFBKOkNRFxQyLUJ4BwAkbW5LRxt7CQ4rCxYafgwFXlIoLx4UbE1hbXMYAmwbJzkvET0NYxMQQFphd0xQBwEyKFlLRWJpMS1kPzsNVAYJdVEpKxpfCR9hcHMuCzckbBADCxYGSCEUX1U3IwNESD4oLz8CCyVDYmpqRQEEHjMQRVEvPkwLRiEuLjIHNS4oOy84XyUCWRc3WEYCIgVaAkVjHT8KHCc7BT8jR1tpEENRF1guKQ1aRhktbW5LLCw6NiskBhdNXgYGHxYVLxRCKgwjKD9JTEhpYmpqER5NYwoLUhR8ajlyDwBzYz0OEmp5bmp5V0JPEFNdFwd3Y2YWRk1hOT9FNS06Kz4jChxDDUMkc10seEJYAxppfX1eSWJkc3x6SVJTHlJJGxRxY2YWRk1hOT9FJyMqKS04CgcNVDcDVloyOg1EAwMiNHNWRXJncH9ARVJDEBcdGXYgKQdRFAI0IzcoCi4mMHlqWFIgXw8eRQdvLB5ZCz8GD3taVW5pc3pmRUBWGWlRFxRhPgAYIAIvOXNWRQcnNydkIx0NRE07QkYgQEwWRk01IX0/ADo9ESMwAFJeEFJHPRRhakxCCkMVKCsfJi0lLTh5RU9DcwwdWEZyZApECQATChFDV3d8bmp8VV5DBlNYPRRhakxCCkMVKCsfRX9pYGhARVJDEBcdGWIoOQVUCghhcHMNBC46J0BqRVJDRA9fZ1UzLwJCRlBhPjRhRWJpYiYlBhMPEBAFRVsqL0wLRiQvPicKCyEsbCQvElpBZSoiQ0YuIQkUT1ZhPicZCiksbAklCR0REF5RdFstJR4FSAszIj45IgBhcH9/SVJVAE9RAQRocUxFEh8uJjZFMSogISEkAAEQEF5RBQ9hORhECQYkYwMKFycnNmp3RQYPOkNRFxQtJQ9XCk0iIiEFADBpf2oDCwEXUQ0SUhovLxseRDgIDjwZCyc7YGNxRREMQg0URRoCJR5YAx8TLDcCEDFpf2ofIRsOHg0UQBxxZkwAT1ZhLjwZCyc7bBorFxcNRENMF0AtQEwWRk0SOCEdDDQoLmQVCx0XWQUIcEEoalEWFQpLbXNLRRE8MDwjExMPHjwfWEAoLBV6Bw8kIXNWRTYlSGpqRVIRVRcERVphOQs8AwMlR1kNECwqNiMlC1IwRREHXkIgJkJFAxkPIicCAyssMGI8THhDEENRZEEzPAVABwFvHicKESdnLCU+DBQKVRE0WVUjJglSRlBhO1lLRWJpKyxqE1IXWAYfPRRhakwWRk1hIDIAAAwmNiMsDBcRdhEQWlFpY2YWRk1hbXNLRSsvYhk/FwQKRgIdGWsiJQJYRhkpKD1LFyc9NzgkRRcNVGlRFxRhakwWRj40PyUCEyMlbBUpChwNEF5RZUEvGQlEEAQiKH0jACM7NigvBAZZcwwfWVEiPkRQEwMiOToEC2pgSGpqRVJDEENRFxRhagVQRgMuOXM4EDA/KzwrCVwwRAIFUhovJRhfAAQkPxYFBCAlJy5qERoGXkMDUkA0OAIWAwMlR3NLRWJpYmpqRVJDEA8eVFUtajMaRgUzPXNWRRc9KyY5SxQKXgc8TmAuJQIeT2dhbXNLRWJpYmpqRVIKVkMfWEBhIh5GRhkpKD1LFyc9NzgkRRcNVGlRFxRhakwWRk1hbXMHCiEoLmokABMRVRAFGxQlIx9CRlBhIzoHSWIkIz4iSxoWVwZ7FxRhakwWRk1hbXNLAy07YhVmRQZDWQ1RXkQgIx5FTj8uIj5FAic9Fj0jFgYGVBBZHh1hLgM8Rk1hbXNLRWJpYmpqRVJDEA8eVFUtaggWW00UOToHFmwtKzk+BBwAVUsZRURvGgNFDxkoIj1HRTZnMCUlEVwzXxAYQ10uJEU8Rk1hbXNLRWJpYmpqRVJDEAoXF1BhdkxSDx41bScDACxpJiM5EVJeEAdKF1okKx5TFRlhcHMfRScnJkBqRVJDEENRFxRhakxTCAlLbXNLRWJpYmpqRVJDWQVRZEEzPAVABwFvEj0EESsvOwYrBxcPEBcZUlpLakwWRk1hbXNLRWJpYmpqRRsFEA0UVkYkORgWBwMlbTcCFjZpfndqNgcRRgoHVlhvGRhXEghvIzwfDCQgJzgYBBwEVUMFX1EvQEwWRk1hbXNLRWJpYmpqRVJDEENRZEEzPAVABwFvEj0EESsvOwYrBxcPHjUYRF0jJgkWW001PyYOb2JpYmpqRVJDEENRFxRhakwWRk1hHiYZEys/IyZkOhwMRAoXTnggKAlaSDkkNSdLWGJhYKjQxVJGQ0M/cnUTao628k1kKXMYETctMWhjXxQMQg4QQxwvLw1EAx41Yz0KCCdlYicrERpNVg8eWEZpLgVFEkRoR3NLRWJpYmpqRVJDEENRFxQkJh9TbE1hbXNLRWJpYmpqRVJDEENRFxRhGRlEEAQ3LD9FOiwmNiMsHD4CUgYdGWIoOQVUCghhcHMNBC46J0BqRVJDEENRFxRhakwWRk1hKD0Pb2JpYmpqRVJDEENRF1EvLmYWRk1hbXNLRScnJmNARVJDEAYfUz4kJAg8bEBsbRIFEStkJTgrB1KBsPdRVkE1JUFQDx8kPnM4FDcgMCcLBxsPWRcIdFUvKQlaRhopKD1LAjAoICgvAXgFRQ0SQ10uJExlEx83JCUKCWw6Jz4LCwYKdxEQVRw3Y2YWRk1hHiYZEys/IyZkNgYCRAZfVlo1IytEBw9hcHMdb2JpYmojA1IVEAIfUxQvJRgWNRgzOzodBC5nHS04BBAgXw0fF0ApLwI8Rk1hbXNLRWJkb2oGDAEXVQ1RUVszagtEBw9hKCUOCzZyYj4iAFIEUQ4UF1IoOAlFRjk2JCAfACYaMz8jFx8kQgITF0MpLwIWBQw0Kjsfb2JpYmpqRVJDXAwSVlhhLR5XBD8EbW5LMDYgLjlkFxcQXw8HUmQgPgQeRD8kPT8CBiM9Jy4ZER0RUQQUGXE3LwJCFUMVOjoYESctETs/DAAOdxEQVRZoQEwWRk1hbXNLDCRpJTgrByAmEAIfUxQmOA1UNChvAj0oCSssLD4PExcNREMFX1EvQEwWRk1hbXNLRWJpYhk/FwQKRgIdGWsmOA1UJQIvI3NWRSU7IygYIFwsXiAdXlEvPilAAwM1dxAECywsIT5iAwcNUxcYWFppZEIYT2dhbXNLRWJpYmpqRVJDEENRXlJhJANCRj40PyUCEyMlbBk+BAYGHgIfQ10GOA1URhkpKD1LFyc9NzgkRRcNVGlRFxRhakwWRk1hbXNLRWJpNis5DlwUUQoFHwRvelkfbE1hbXNLRWJpYmpqRVJDEEMjUlkuPglFSAsoPzZDRxE4NyM4CDECXgAUWxZoQEwWRk1hbXNLRWJpYmpqRVIwRAIFRBokOQ9XFgglCiEKBzFpf2oZERMXQ00URFcgOglSIR8gLyBLTmJ4SGpqRVJDEENRFxRhaglYAkRLbXNLRWJpYmovCxZpEENRF1EtOQlfAE0vIidLE2IoLC5qNgcRRgoHVlhvFQtEBw8CIj0FRTYhJyRARVJDEENRFxQSPx5ADxsgIX00AjAoIAklCxxZdAoCVFsvJAlVEkVodnM4EDA/KzwrCVw8VxEQVXcuJAIWW00vJD9hRWJpYi8kAXgGXgd7PRlsaihTBxkpbTAEECw9JzhANxcOXxcURBoiJQJYAw41ZXEvACM9KmhmRRQWXgAFXlsvYkUWNRkgOSBFAScoNiI5RU9DYxcQQ0dvLglXEgUybXhLVGIsLC5jb3hOHUOToqSj3/zU8/2j2MOJ8NKr19qo8OKBpfOToqSj3/zU8/2j2MOJ8NKr19qo8OKBpfOToqSj3/zU8/2j2MOJ8NKr19qo8OKBpfOToqSj3/zU8/2j2MOJ8NKr19qo8OKBpfOToqSj3/zU8/2j2MOJ8NKr19qo8OKBpfOToqSj3/zU8/2j2MOJ8NKr19qo8OKBpfOToqSj3/zU8/2j2MOJ8NKr19qo8OKBpfOToqSj3/zU8/2j2MOJ8NKr19qo8OKBpfOToqSj3/zU8/2j2MOJ8NKr19qo8OKBpfOToqSj3/zU8/1LYH5LXWxpDwsJLTstdUMwYmAOBy1iLyIPbbHr8WIINz4lRSEIWQ8dF3cpLw9dbEBsbbH+9aDc0qjf9ZD2oIHkp9bU2o6j9o/U3bH+9aDc0qjf9ZD2oIHkp9bU2o6j9o/U3bH+9aDc0qjf9ZD2oIHkp9bU2o6j9o/U3bH+9aDc0qjf9ZD2oIHkp9bU2o6j9o/U3bH+9aDc0qjf9ZD2oIHkp9bU2o6j9o/U3bH+9aDc0qjf9ZD2oIHkp9bU2o6j9o/U3bH+9aDc0qjf9ZD2oIHkp9bU2o6j9o/U3bH+9aDc0qjf9ZD2oIHkp9bU2o6j9o/U3bH+9aDc0qjf9ZD2oIHkp9bU2o6j9o/U3bH+9aDc0qjf9XhOHUMlX1FhOQlEEAgzbTcEADFzYmoZDhsPXAAZUlcqHxxSBxkkdxoFEy0iJwkmDBcNREsBW1U4Lx4aRgokIzYZBDYmMGZqBAAEQ0p7GhlhPQRTFAhhLCEMFmIlLSUhFlIPWQgUF09hPhVGA018bXEIDDAqLi9oGVAXQgYQU1koJgAUSk0jIiYFASM7OxkjHxdDDUM/GxQ1Kx5RAxluPTwYDDYgLSRlBhcNRAYDFwlhHkAWSENvbS5hSG9pFiIvRREPWQYfQxQsPx9CRh8kOSYZC2IoYiQ/CBAGQkMYWRQaekIYVzBhOTsKEWIlIyQuFlIKXhAYU1FhPgRTRgozKDYFRTgmLC9ASF9DUwYfQ1EzLwgWCQNhGXMcDDYhYiIrCRRORwoVQ1xhKANDCAkgPyo4DDgsbXhkb19OOk5cF2c1OA1CAwo4d3MZACMtYj4iAFIXUREWUkBhLAVTCglhKyEECGIoMC05RVoUVUMFRU1hLxpTFBRhLjwGCC0nYiQrCBdKHmlcGhQILExBA00iLD1MEWIvKyQuRRsXHEMXVlgtag5XBQZhOTxLBGI6Nis+DBFDRgIdQlFhPgRTRhgyKCFLBiMnYj4/CxdNOg8eVFUtaiFXBQUoIzZLWGIyYhk+BAYGEF5RTD5hakwWBxg1IgAADC4lISIvBhlDDUMXVlgyL0A8Rk1hbTIeES0aKSMmCRELVQAac1EtKxUWW01xYVlLRWJpJCsmCRACUwgnVlg0L0wLRl1veH9LRWJpb2dqChwPSUMERFElahteAwNhIzxLESM7JS8+RRQKVQ8VF10yagVYRgwzKiBhRWJpYi4vBwcEYBEYWUBhakwLRgsgISAOSWJpYmdnRQIRWQ0FRBQgOAtFRgIvLjZLEiosLGo+ChUEXAYVPUk8QGYbS00PAgcuX2IbLSgmCgpDVAwURBQPBTgWBwEtIiRLFycoJiMkAlIRVk0+WXctIwlYEiQvOzwAAGJhNTgjERdOXw0dTh1vQEEbRjokbTAKC2U9YjkrExdDRAsUF1szIwtfCAwtbTsKCyYlJzhkRTsFEBcZUhQmKwFTQR5hGBpLFic9MWojEV5DXxYDRBQ2IwBaRh8kPT8KBidpKz5ASF9DGAIfUxQ3Iw9TRhskPyAKTGxpFSs+BhoHXwRRXUEyPkxEA0AgPSMHDCc6YiU/FwFDVRUURU1hekIDFU02JCcDCjc9YikiABEIWQ0WGT4tJQ9XCk0eJTIFAS4sMAspERsVVUNMF1IgJh9TbAEuLjIHRR0lIzk+IRcBRQQlXlkkalEWVmdLYH5LMTAgJzlqAAQGQhpRVFssJwNYRgMgIDZLAy07Yj4iAFJBRAIDUFE1ahxZFQQ1JDwFR2JmYmgpABwXVRFTF1IoLwBSRgQvbTIZAjFnSCYlBhMPEAUEWVc1IwNYRgg5OSEKBjYdIzgtAAZLUREWRB1LakwWRgQnbScSFSdhIzgtFltDTl5RFUAgKABTRE01JTYFRTAsNj84C1INWQ9RUlolQEwWRk1sYHMvDDAsIT5qCwcOVREYVBQnIwlaAh5LbXNLRSQmMGoVSVIIEAofF10xKwVEFUU6R3NLRWJpYmpqRwYCQgQUQxZtak5CBx8mKCc7CjEgNiMlC1BPEEEBWEcoPgVZCE9tbXEIACw9JzhoSVJBUwYfQ1EzGgNFREFLbXNLRWJpYmpoAAoTVQAFUlBjZkwUFggzKzYIERImMSM+DB0NEk9RFVwoPjxZFQQ1JDwFR25pYCQvABYPVUFdPRRhakwWRk1hbykECycKJyQ+AABBHENTVF0zKQBTJQgvOTYZR25pYCcjAQIMWQ0FFRhhaBpXChgkb39hRWJpYjdjRRYMOkNRFxRhakwWCgIiLD9LE2J0Yis4AgE4Wz57FxRhakwWRk0oK3MfHDIsajxjRU9eEEEfQlkjLx4URhkpKD1LFyc9NzgkRQRDVQ0VPRRhakxTCAlLbXNLRW9kYhklCBcXWQ4URBQvLx9CAwlhJD0YDCYsYitqRwgMXgZTF1szak5UCRgvKTIZHGBpNisoCRdpEENRF1IuOExpSk0qbToFRSs5IyM4FloYEEELWFokaEAWRA8uOD0PBDAwYGZqRwEIWQ8dVFwkKQcUSk1jPjgCCS4KKi8pDlBDTUpRU1tLakwWRk1hbXMHCiEoLmo5EBBDDUMQRVMyEQdrbE1hbXNLRWJpKyxqEQsTVUsCQlZoalELRk81LDEHAGBpNiIvC3hDEENRFxRhakwWRk0nIiFLOm5pKXhqDBxDWRMQXkYyYhcWRA4kIycOF2BlYmg6CgEKRAoeWRZtak5CBx8mKCdJSWJrLyMuFR0KXhdTF0loaghZbE1hbXNLRWJpYmpqRVJDEEMYURQ1MxxTTh40LwgAVx9gYnd3RVANRQ4TUkZjahheAwNhPzYfEDAnYjk/BykIAj5RUlolQEwWRk1hbXNLRWJpYi8kAXhDEENRFxRhaglYAmdhbXNLACwtSGpqRVIRVRcERVphJAVabAgvKVlhSG9pEjgvEQYaHRMDXlo1OUxXRhkgLz8ORTYmYj4iAFIAXw0CWFgkakRZCAhhITYdAC5pJi8vFVtpXAwSVlhhLBlYBRkoIj1LATckMgs4AgFLUREWRB1LakwWRgQnbScSFSdhIzgtFltDTl5RFUAgKABTRE01JTYFRTI7KyQ+TVA4aVE6F3AgJAhPO00yJjoHCWIqKi8pDlICQgQCDRZtag1EAR5odnMZADY8MCRqABwHOkNRFxQxOAVYEkVjFgpZLmINIyQuHC9DDV5MF0cqIwBaRg4pKDAARSM7JTlqWE9eEkp7FxRhagpZFE0qYXMdRSsnYjorDAAQGAIDUEdoaghZbE1hbXNLRWJpKyxqEQsTVUsHHhR8d0wUEgwjITZJRTYhJyRARVJDEENRFxRhakwWFh8oIydDR2JpYGZqDl5DEl5RTBZoQEwWRk1hbXNLRWJpYiwlF1IIAk9RQQZhIwIWFgwoPyBDE2tpJiVqFQAKXhdZFRRhakwWRk9tbThZSWJrf2hmRQRRGUMUWVBLakwWRk1hbXNLRWJpMjgjCwZLEkNRShZoQEwWRk1hbXNLAC46J0BqRVJDEENRFxRhakxGFAQvOXtJRWJrbmohSVJBDUFdF0Jtak4eRENvOSobAGo/a2RkR1tBGWlRFxRhakwWRggvKVlLRWJpJyQubxcNVGl7W1siKwAWABgvLicCCixpLT84NhkKXA8yX1EiISRXCAktKCFDFS4oOy84SVIEVQ0URVU1JR4aRgwzKiBCb2JpYmpnSFInVQEEUBQxOAVYEk1pIj0OSDEhLT5qFRcREBceUFMtL0xCCU0gOzwCAWI6MisnTHhDEENRXlJhBw1VDgQvKH04ESM9J2QuABAWVzMDXlo1ag1YAk1pOToIDmpgYmdqOh4CQxc1UlY0LThfCwhobW1LVGI9Ki8kb1JDEENRFxRhFQBXFRkFKDEeAhYgLy9qWFIXWQAaHx1LakwWRk1hbXMPEC85AzgtFloCQgQCHj5hakwWAwMlR1lLRWJpKyxqCx0XEC4QVFwoJAkYNRkgOTZFBDc9LRkhDB4PUwsUVF9hPgRTCGdhbXNLRWJpYmdnRSAGRBYDWV0vLUxYCRkpJD0MRS8oKS85RQYLVUMCUkY3Lx4RFU17BD0dCiksASYjABwXEBcZRVs2ao628k0jOCdLEidpKis8AFINX2lRFxRhakwWRkBsbSQKHGI9LWosCgAUUREVF0AuahheA00uPzoMDCwoLmoiBBwHXAYDFxwTJQ5aCRVhKzwZBystMWo4ABMHWQ0WF3svCQBfAwM1BD0dCiksa2RARVJDEENRFxRsZ0xlCU0oK3MSCjdpNSskEVIXWAZRRVEmPwBXFE0UBHMJBCEibmo+EAANEBcZUhQ1JQtRCghhIjUNRSMnJmo4ABgMWQ1fPRRhakwWRk1hPzYfEDAnSGpqRVIGXgd7PRRhakxfAE0MLDADDCwsbBk+BAYGHgIEQ1sSIQVaCg4pKDAAISclIzNqW1JTEBcZUlpLakwWRk1hbXMfBDEibD0rDAZLfQISX10vL0JlEgw1KH0KEDYmESEjCR4AWAYSXHAkJg1PT2dhbXNLACwtSEBqRVJDHU5RcV0zORgWEh84d3MZADY8MCRqERoGEBcQRVMkPkxCDghhPjYZEyc7YiM+FhcPVkMCUlo1ahlFbE1hbXMHCiEoLmo+BAAEVRdRChQkMhhEBw41GTIZAic9ais4AgFKOkNRFxQoLExCBx8mKCdLESosLGo4AAYWQg1RQ1UzLQlCRggvKVlhRWJpYmdnRTQCXA8TVlcqakRZCAE4bSYYACZpNSIvC1INX0MFVkYmLxgWAAQkITdLAy08LC5qDBxDUREWRB1LakwWRh8kOSYZC2IEIykiDBwGHjAFVkAkZApXCgEjLDAAMyMlNy9AABwHOmkdWFcgJkxQEwMiOToEC2IgLDk+BB4PeAIfU1gkOEQfbE1hbXMHCiEoLmo4A1JeEDYFXlgyZB5TFQItOzY7BDYhamgYAAIPWQAQQ1ElGRhZFAwmKH0uEycnNjlkNhkKXA8SX1EiITlGAgw1KHFCb2JpYmojA1INXxdRRVJhJR4WCAI1bSENXws6A2JoNxcOXxcUcUEvKRhfCQNjZHMfDScnYjgvEQcRXkMXVlgyL0xTCAlLbXNLRW9kYh0YLCYmHSw/e217agJTEAgzbSEOBCZpMCxkKhwgXAoUWUAIJBpZDQhLbXNLRTAvbAUkJh4KVQ0Fflo3JQdTRlBhIiYZNikgLiYJDRcAWysQWVAtLx48Rk1hbQwDBCwtLi84JBEXWRUUFwlhPh5DA2dhbXNLFyc9NzgkRQYRRQZ7UlolQGZaCQ4gIXMNECwqNiMlC1IQRAIDQ2MgPg9eAgImZXphRWJpYiMsRT8CUwsYWVFvFRtXEg4pKTwMRTYhJyRqFxcXRREfF1EvLmYWRk1hADIIDSsnJ2QVEhMXUwsVWFNhd0xCBx4qYyAbBDUnaiw/CxEXWQwfHx1LakwWRk1hbXMcDSslJ2oHBBELWQ0UGWc1KxhTSAw0OTw4DislLikiABEIEAwDF3kgKQRfCAhvHicKESdnJi8oEBUzQgofQxQlJWYWRk1hbXNLRWJpYmpnSFIxVU4GRV01L0xCDghhJTIFAS4sMGo6AAAKXwcYVFUtJhUWDwNhLjIYAGI9Ki9qAhMOVUQCF2EIah5TSx4kOXMCEWxDYmpqRVJDEENRFxRhZ0EWMQhhLjIFQjZpISIvBhlDRwseF1s2JB8WDxlhr9P/RTUsYiA/FgZDXxUURUMzIxhTSGdhbXNLRWJpYmpqRVIKXhAFVlgtAg1YAgEkP3tCb2JpYmpqRVJDEENRF0AgOQcYEQwoOXtaS3JgSGpqRVJDEENRUlolQEwWRk1hbXNLKCMqKiMkAFw8RwIFVFwlJQsWW00vJD9hRWJpYi8kAVtpVQ0VPT4nPwJVEgQuI3MmBCEhKyQvSwEGRCIEQ1sSIQVaCg4pKDAATTRgSGpqRVIuUQAZXlokZD9CBxkkYzIeES0aKSMmCRELVQAaFwlhPGYWRk1hJDVLE2I9Ki8kRRsNQxcQW1gJKwJSCggzZXpQRTE9Izg+MhMXUwsVWFNpY0xTCAlLKD0Pb0gvNyQpERsMXkM8VlcpIwJTSB4kORcOBzcuEjgjCwZLRkp7FxRhaiFXBQUoIzZFNjYoNi9kARcBRQQhRV0vPkwLRhtLbXNLRSsvYjxqERoGXkMYWUc1KwBaLgwvKT8OF2pgeWo5ERMRRDQQQ1cpLgNRTkRhKD0PbycnJkBASF9D0vbh1aHRqPmmhPjRr8b7h9fZoN/ah+fz0vbh1aHRqPmmhPjRr8b7h9fZoN/ah+fz0vbh1aHRqPmmhPjRr8b7h9fZoN/ah+fz0vbh1aHRqPmmhPjRr8b7h9fZoN/ah+fz0vbh1aHRqPmmhPjRr8b7h9fZoN/ah+fz0vbh1aHRqPmmhPjRr8b7h9fZoN/ah+fz0vbh1aHRqPmmhPjRr8b7h9fZoN/ah+fz0vbh1aHRqPmmhPjRr8b7h9fZoN/ah+fz0vbh1aHRqPmmhPjRr8b7h9fZoN/ah+fz0vbh1aHRqPmmbEBsbWpFRQMcFgVqNTsgezYhPRlsao6j9o/U3bH+9aDc0qjf9ZD2oIHkp9bU2o6j9o/U3bH+9aDc0qjf9ZD2oIHkp9bU2o6j9o/U3bH+9aDc0qjf9ZD2oIHkp9bU2o6j9o/U3bH+9aDc0qjf9ZD2oIHkp9bU2o6j9o/U3bH+9aDc0qjf9ZD2oIHkp9bU2o6j9o/U3bH+9aDc0qjf9ZD2oIHkp9bU2o6j9o/U3bH+9aDc0qjf9ZD2oIHkp9bU2o6j9o/U3bH+9aDc0qjf9ZD2oIHkp9bU2o6j9o/U3bH+9aDc0qjf9ZD2oIHkp9bU2o6j9o/U3bH+9UglLSkrCVIiRRceZ10iIRlGRlBhNnM4ESM9J2p3RQlDQhYfWV0vLUwLRgsgISAOSWI7IyQtAFJeEFJDGxQoJBhTFBsgIXNWRXJnd2o3RQ9pVhYfVEAoJQIWJxg1IgMCBik8MmQ5ERMRREtYPRRhakxfAE0AOCcENSsqKT86SyEXURcUGUY0JAJfCAphOTsOC2I7Jz4/FxxDVQ0VPRRhakx3ExkuHToIDjc5bBk+BAYGHhEEWVooJAsWW001PyYOb2JpYmofERsPQ00dWFsxYgpDCA41JDwFTWtpMC8+EAANECIEQ1sRIw9dEx1vHicKESdnKyQ+AAAVUQ9RUlolZmYWRk1hbXNLRSQ8LCk+DB0NGEpRRVE1Px5YRiw0OTw7DCEiNzpkNgYCRAZfRUEvJAVYAU0kIzdHRSQ8LCk+DB0NGEp7FxRhakwWRk1hbXNLCS0qIyZqOl5DWBEBFwlhHxhfCh5vKzoFAQ8wFiUlC1pKOkNRFxRhakwWRk1hbToNRSwmNmoiFwJDRAsUWRQzLxhDFANhKD0Pb2JpYmpqRVJDEENRF1IuOExpSk0oOTYGRSsnYiM6BBsRQ0sjWFssZAtTEiQ1KD4YTWtgYi4lb1JDEENRFxRhakwWRk1hbXMCA2IcNiMmFlwHWRAFVloiL0ReFB1vHTwYDDYgLSRmRRsXVQ5fRVsuPkJmCR4oOToEC2tpfndqJAcXXzMYVF80OkJlEgw1KH0ZBCwuJ2o+DRcNOkNRFxRhakwWRk1hbXNLRWJpYmpqSF9DZwIdXBQuPAlERhkpKHMCESckYjgrERoGQkMFX1UvaghfFAgiOXMfAC4sMiU4EVIXX0MQQVsoLkxFFggkKXMNCSMuSGpqRVJDEENRFxRhakwWRk1hbXNLDTA5bAkMFxMOVUNMF3cHOA1bA0MvKCRDDDYsL2Q4Ch0XHjMeRF01IwNYRkZhGzYIES07cWQkAAVLAE9RBRhhekUfbE1hbXNLRWJpYmpqRVJDEENRFxRhGRhXEh5vJCcOCDEZKykhABZDDUMiQ1U1OUJfEggsPgMCBiksJmphRUNpEENRFxRhakwWRk1hbXNLRWJpYmo+BAEIHhQQXkBpekIHU0RLbXNLRWJpYmpqRVJDEENRF1EvLmYWRk1hbXNLRWJpYmovCxZpEENRFxRhakxTCAloRzYFAUgvNyQpERsMXkMwQkAuGgVVDRgxYyAfCjJha2oLEAYMYAoSXEExZD9CBxkkYyEeCywgLC1qWFIFUQ8CUhQkJAg8bEBsbbH+9aDc0qjf9ZD2oIHkp9bU2o6j9o/U3bH+9aDc0qjf9ZD2oIHkp9bU2o6j9o/U3bH+9aDc0qjf9ZD2oIHkp9bU2o6j9o/U3bH+9aDc0qjf9ZD2oIHkp9bU2o6j9o/U3bH+9aDc0qjf9ZD2oIHkp9bU2o6j9o/U3bH+9aDc0qjf9ZD2oIHkp9bU2o6j9o/U3bH+9aDc0qjf9ZD2oIHkp9bU2o6j9o/U3bH+9aDc0qjf9ZD2oIHkp9bU2o6j9o/U3bH+9aDc0qjf9ZD2oIHkp9bU2o6j9o/U3bH+9aDc0qjf9XhOHUNABxphByNgIyAEAwdLTTEoJC9qFxMNVwYCDBQmKwFTRgUgPnMKRTEsMDwvF18QWQcUF0cxLwlSRg4pKDAATEhkb2qo8OKBpfOToqSj3/zU8/2j2MOJ8NKr19qo8OKBpfOToqSj3/zU8/2j2MOJ8NKr19qo8OKBpfOToqSj3/zU8/2j2MOJ8NKr19qo8OKBpfOToqSj3/zU8/2j2MOJ8NKr19qo8OKBpfOToqSj3/zU8/2j2MOJ8NKr19qo8OKBpfOToqSj3/zU8/2j2MOJ8NKr19qo8OKBpfOToqSj3/zU8/2j2MOJ8NKr19qo8OKBpfOToqSj3/zU8/2j2MOJ8NKr19qo8OKBpfOToqSj3/zU8/2j2MOJ8NKr19qo8OKBpfOToqRLJgNVBwFhADwdAC8sLD5qWFIYEDAFVkAkalEWHWdhbXNLEiMlKRk6ABcHEF5RBgFtagZDCx0RIiQOF2J0Yn96SVIKXgU7QlkxalEWAAwtPjZHRSwmISYjFVJeEAUQW0ckZmYWRk1hKz8SRX9pJCsmFhdPEAUdTmcxLwlSRlBheGNHRSMnNiMLIzlDDUMFRUEkZkxFBxskKQMEFmJ0YiQjCV5pEENRF1Y4Og1FFT4xKDYPJiM5YndqAxMPQwZdFxlsagVQRhgyKCFLEiMnNjlqDRsEWAYDF0ApKwIWNSwHCAwmJBoWERoPIDZpTU9RaFcuJAIWW006MHMWb0glLSkrCVIFRQ0SQ10uJExXFh0tNBseCCMnLSMuTVtpEENRF1guKQ1aRjJtbQxHRSo8L2p3RScXWQ8CGVIoJAh7HzkuIj1DTHlpKyxqCx0XEAsEWhQ1IglYRh8kOSYZC2IsLC5ARVJDEAsEWhoWKwBdNR0kKDdLWGIELTwvCBcNRE0iQ1U1L0JBBwEqHiMOACZDYmpqRQIAUQ8dH1I0JA9CDwIvZXpLDTckbAA/CAIzXxQURRR8aiFZEAgsKD0fSxE9Iz4vSxgWXRMhWEMkOExTCAloR3NLRWI5ISsmCVoFRQ0SQ10uJEQfRgU0IH0+FicDNyc6NR0UVRFRChQ1OBlTRggvKXphACwtSCw/CxEXWQwfF3kuPAlbAwM1YyAOERUoLiEZFRcGVEsHHj5hakwWEE18bScECzckIC84TQRKEAwDFwV0QEwWRk0oK3MFCjZpDyU8AB8GXhdfZEAgPgkYBBQxLCAYNjIsJy4JBAJDUQ0VF0JhdEx1CQMnJDRFNgMPBxUHJCo8YzM0cnBhPgRTCE03bW5LJi0nJCMtSyEidiYuenUZFT9mIygFbTYFAUhpYmpqKB0VVQ4UWUBvGRhXEghvOjIHDhE5Jy8uRU9DRmlRFxRhKxxGChQJOD4KCy0gJmJjbxcNVGkXQloiPgVZCE0MIiUOCCcnNmQ5AAYpRQ4BZ1s2Lx4eEERhADwdAC8sLD5kNgYCRAZfXUEsOjxZEQgzbW5LES0nNycoAABLRkpRWEZhf1wNRgwxPT8SLTckIyQlDBZLGUMUWVBLLBlYBRkoIj1LKC0/JycvCwZNQwYFflonABlbFkU3ZFlLRWJpDyU8AB8GXhdfZEAgPgkYDwMnByYGFWJ0YjxARVJDEAoXF0JhKwJSRgMuOXMmCjQsLy8kEVw8UwwfWRooJAp8EwAxbScDACxDYmpqRVJDEEM8WEIkJwlYEkMeLjwFC2wgLCwAEB8TEF5RYkckOCVYFhg1HjYZEysqJ2QAEB8TYgYAQlEyPlZ1CQMvKDAfTSQ8LCk+DB0NGEp7FxRhakwWRk1hbXNLDCRpLCU+RT8MRgYcUlo1ZD9CBxkkYzoFAwg8LzpqERoGXkMDUkA0OAIWAwMlR3NLRWJpYmpqRVJDEA8eVFUtajMaRjJtbTseCGJ0Yh8+DB4QHgUYWVAMMzhZCQNpZFlLRWJpYmpqRVJDEEMYURQpPwEWEgUkI3MDEC9zASIrCxUGYxcQQ1FpDwJDC0MJOD4KCy0gJhk+BAYGZBoBUhoLPwFGDwMmZHMOCyZDYmpqRVJDEEMUWVBoQEwWRk0kISAODCRpLCU+RQRDUQ0VF3kuPAlbAwM1YwwICiwnbCMkAzgWXRNRQ1wkJGYWRk1hbXNLRQ8mNC8nABwXHjwSWFovZAVYACc0ICNRISs6ISUkCxcAREtYDBQMJRpTCwgvOX00Bi0nLGQjCxQpRQ4BFwlhJAVabE1hbXMOCyZDJyQubxQWXgAFXlsvaiFZEAgsKD0fSzEsNgQlBh4KQEsHHj5hakwWKwI3KD4OCzZnET4rERdNXgwSW10xalEWEGdhbXNLDCRpNGorCxZDXgwFF3kuPAlbAwM1YwwICiwnbCQlBh4KQEMFX1EvQEwWRk1hbXNLKC0/JycvCwZNbwAeWVpvJANVCgQxbW5LNzcnES84ExsAVU0iQ1ExOglSXC4uIz0OBjZhJD8kBgYKXw1ZHj5hakwWRk1hbXNLRWIgJGokCgZDfQwHUlkkJBgYNRkgOTZFCy0qLiM6RQYLVQ1RRVE1Px5YRggvKVlLRWJpYmpqRVJDEEMdWFcgJkxVDgwzbW5LKS0qIyYaCRMaVRFfdFwgOA1VEggzdnMCA2InLT5qBhoCQkMFX1Evah5TEhgzI3MOCyZDYmpqRVJDEENRFxRhLANERjJtbSNLDCxpKzorDAAQGAAZVkZ7DQlCIggyLjYFASMnNjliTFtDVAx7FxRhakwWRk1hbXNLRWJpYiMsRQJZeRAwHxYDKx9TNgwzOXFCRSMnJmo6SzECXiAeW1goLgkWEgUkI3MbSwEoLAklCR4KVAZRChQnKwBFA00kIzdhRWJpYmpqRVJDEENRUlolQEwWRk1hbXNLACwta0BqRVJDVQ8CUl0nagJZEk03bTIFAWIELTwvCBcNRE0uVFsvJEJYCQ4tJCNLESosLEBqRVJDEENRF3kuPAlbAwM1YwwICiwnbCQlBh4KQFk1XkciJQJYAw41ZXpQRQ8mNC8nABwXHjwSWFovZAJZBQEoPXNWRSwgLkBqRVJDVQ0VPVEvLmZaCQ4gIXMNECwqNiMlC1IQRAIDQ3ItM0QfbE1hbXMHCiEoLmoVSVILQhNdF1w0J0wLRjg1JD8YSyQgLC4HHCYMXw1ZHg9hIwoWCAI1bTsZFWImMGokCgZDWBYcF0ApLwIWFAg1OCEFRScnJkBqRVJDXAwSVlhhKBoWW00IIyAfBCwqJ2QkAAVLEiEeU00XLwBZBQQ1NHFCXmIrNGQHBAolXxESUhR8ajpTBRkuP2BFCyc+ansvXF5SVVpdBlF4Y1cWBBtvGzYHCiEgNjNqWFI1VQAFWEZyZAJTEUVodnMJE2wZIzgvCwZDDUMZRURLakwWRgEuLjIHRSAuYndqLBwQRAIfVFFvJAlBTk8DIjcSIjs7LWhjXlIBV008VkwVJR5HEwhhcHM9ACE9LTh5SxwGR0tAUg1tewkPSlwkdHpQRSAubBpqWFJSVVdKF1YmZDxXFAgvOXNWRSo7MkBqRVJDfQwHUlkkJBgYOQ4uIz1FAy4wABxmRT8MRgYcUlo1ZDNVCQMvYzUHHAAOYndqBwRPEAEWPRRhakxeEwBvHT8KESQmMCcZERMNVENMF0AzPwk8Rk1hbR4EEyckJyQ+Sy0AXw0fGVItMzlGAgw1KHNWRRA8LBkvFwQKUwZfZVEvLglENRkkPSMOAXgKLSQkABEXGAUEWVc1IwNYTkRLbXNLRWJpYmojA1INXxdRels3LwFTCBlvHicKESdnJCYzRQYLVQ1RRVE1Px5YRggvKVlLRWJpYmpqRR4MUwIdF1cgJ0wLRhouPzgYFSMqJ2QJEAARVQ0FdFUsLx5XbE1hbXNLRWJpLiUpBB5DXUNMF2IkKRhZFF5vIzYcTWtDYmpqRVJDEEMYURQUOQlELwMxOCc4ADA/KykvXzsQewYIc1s2JERzCBgsYxgOHAEmJi9kMltDEENRFxRhakxCDggvbT5LWGIkYmFqBhMOHiA3RVUsL0J6CQIqGzYIES07Yi8kAXhDEENRFxRhagVQRjgyKCEiCzI8NhkvFwQKUwZLfkcKLxVyCRovZRYFEC9nCS8zJh0HVU0iHhRhakwWRk1hbScDACxpL2p3RR9DHUMSVllvCSpEBwAkYx8ECikfJyk+CgBDVQ0VPRRhakwWRk1hJDVLMDEsMAMkFQcXYwYDQV0iL1Z/FSYkNBcEEixhByQ/CFwoVRoyWFAkZC0fRk1hbXNLRWJpNiIvC1IOEF5RWhRsag9XC0MCCyEKCCdnECMtDQY1VQAFWEZhLwJSbE1hbXNLRWJpKyxqMAEGQiofR0E1GQlEEAQiKGkiFgksOw4lEhxLdQ0EWhoKLxV1CQkkYxdCRWJpYmpqRVJDRAsUWRQsalEWC01qbTAKCGwKBDgrCBdNYgoWX0AXLw9CCR9hKD0Pb2JpYmpqRVJDWQVRYkckOCVYFhg1HjYZEysqJ3ADFjkGSSceQFppDwJDC0MKKCooCiYsbBk6BBEGGUNRFxRhPgRTCE0sbW5LCGJiYhwvBgYMQlBfWVE2YlwaRlxtbWNCRScnJkBqRVJDEENRF10najlFAx8IIyMeEREsMDwjBhdZeRA6Uk0FJRtYTigvOD5FLicwASUuAFwvVQUFZFwoLBgfRhkpKD1LCGJ0YidqSFI1VQAFWEZyZAJTEUVxYXNaSWJ5a2ovCxZpEENRFxRhakxfAE0sYx4KAiwgNj8uAFJdEFNRQ1wkJExbRlBhIH0+Cys9YmBqKB0VVQ4UWUBvGRhXEghvKz8SNjIsJy5qABwHOkNRFxRhakwWBBtvGzYHCiEgNjNqWFIOOkNRFxRhakwWBApvDhUZBC8sYndqBhMOHiA3RVUsL2YWRk1hKD0PTEgsLC5ACR0AUQ9RUUEvKRhfCQNhPicEFQQlO2Jjb1JDEEMXWEZhFUAWDU0oI3MCFSMgMDliHlAFXBokR1AgPgkUSk8nISopM2BlYCwmHDAkEh5YF1AuQEwWRk1hbXNLCS0qIyZqBlJeEC4eQVEsLwJCSDIiIj0FPikUSGpqRVJDEENRXlJhKUxCDggvR3NLRWJpYmpqRVJDEAoXF0A4OglZAEUiZHNWWGJrEAgSNhERWRMFdFsvJAlVEgQuI3FLESosLGopXzYKQwAeWVokKRgeT00kISAORSFzBi85EQAMSUtYF1EvLmYWRk1hbXNLRWJpYmoHCgQGXQYfQxoeKQNYCDYqEHNWRSwgLkBqRVJDEENRF1EvLmYWRk1hKD0Pb2JpYmomChECXEMuGxQeZkxeEwBhcHM+ESslMWQsDBwHfRolWFsvYkU8Rk1hbToNRSo8L2o+DRcNEAsEWhoRJg1CAAIzIAAfBCwtYndqAxMPQwZRUlolQAlYAmcnOD0IESsmLGoHCgQGXQYfQxoyLxhwChRpO3pLKC0/JycvCwZNYxcQQ1FvLABPRlBhO2hLDCRpNGo+DRcNEBAFVkY1DABPTkRhKD8YAGI6NiU6Ix4aGEpRUlolaglYAmcnOD0IESsmLGoHCgQGXQYfQxoyLxhwChQSPTYOAWo/a2oHCgQGXQYfQxoSPg1CA0MnISo4FScsJmp3RQYMXhYcVVEzYhofRgIzbWZbRScnJkAsEBwARAoeWRQMJRpTCwgvOX0YADYILD4jJDQoGBVYPRRhakx7CRskIDYFEWwaNis+AFwCXhcYdnIKalEWEGdhbXNLDCRpNGorCxZDXgwFF3kuPAlbAwM1YwwICiwnbCskERsidihRQ1wkJGYWRk1hbXNLRQ8mNC8nABwXHjwSWFovZA1YEgQACxhLWGIFLSkrCSIPURoURRoILgBTAlcCIj0FACE9aiw/CxEXWQwfHx1LakwWRk1hbXNLRWJpKyxqCx0XEC4eQVEsLwJCSD41LCcOSyMnNiMLIzlDRAsUWRQzLxhDFANhKD0Pb2JpYmpqRVJDEENRF0QiKwBaTgs0IzAfDC0namNqMxsRRBYQW2EyLx4MJQwxOSYZAAEmLD44Ch4PVRFZHg9hHAVEEhggIQYYADBzASYjBhkhRRcFWFpzYjpTBRkuP2FFCyc+amNjRRcNVEp7FxRhakwWRk0kIzdCb2JpYmovCQEGWQVRWVs1ahoWBwMlbR4EEyckJyQ+Sy0AXw0fGVUvPgV3ICZhOTsOC0hpYmpqRVJDEC4eQVEsLwJCSDIiIj0FSyMnNiMLIzlZdAoCVFsvJAlVEkVodnMmCjQsLy8kEVw8UwwfWRogJBhfJysKbW5LCyslSGpqRVIGXgd7UlolQApDCA41JDwFRQ8mNC8nABwXHhAQQVERJR8eT2dhbXNLCS0qIyZqOl5DWBEBFwlhHxhfCh5vKzoFAQ8wFiUlC1pKC0MYURQpOBwWEgUkI3MmCjQsLy8kEVwwRAIFUhoyKxpTAj0uPnNWRSo7MmQaCgEKRAoeWQ9hOAlCEx8vbScZECdpJyQubxcNVGkXQloiPgVZCE0MIiUOCCcnNmQ4ABECXA8hWEdpY2YWRk1hJDVLKC0/JycvCwZNYxcQQ1FvOQ1AAwkRIiBLESosLGofERsPQ00FUlgkOgNEEkUMIiUOCCcnNmQZERMXVU0CVkIkLjxZFUR6bSEOETc7LGo+FwcGEAYfUz4kJAg8KgIiLD87CSMwJzhkJhoCQgISQ1EzCwhSAwl7DjwFCycqNmIsEBwARAoeWRxoQEwWRk01LCAASzUoKz5iVVxVGVhRVkQxJhV+EwAgIzwCAWpgSGpqRVIKVkM8WEIkJwlYEkMSOTIfAGwvLjNqERoGXkMCQ1UzPipaH0VobTYFAUgsLC5jb3hOHUOToqSj3/zU8/2j2MOJ8NKr19qo8OKBpfOToqSj3/zU8/2j2MOJ8NKr19qo8OKBpfOToqSj3/zU8/2j2MOJ8NKr19qo8OKBpfOToqSj3/zU8/2j2MOJ8NKr19qo8OKBpfOToqSj3/zU8/2j2MOJ8NKr19qo8OKBpfOToqSj3/zU8/2j2MOJ8NKr19qo8OKBpfOToqSj3/zU8/2j2MOJ8NKr19qo8OKBpfOToqSj3/zU8/2j2MOJ8NKr19qo8OKBpfOToqSj3/zU8/2j2MOJ8NKr19qo8OKBpfOToqSj3/zU8/1LYH5LVHNnYhwDNicifDB7GhlhqPmmhPjRr8b7h9fZoN/ah+fz0vbh1aHRqPmmhPjRr8b7h9fZoN/ah+fz0vbh1aHRqPmmhPjRr8b7h9fZoN/ah+fz0vbh1aHRqPmmhPjRr8b7h9fZoN/ah+fz0vbh1aHRqPmmhPjRr8b7h9fZoN/ah+fz0vbh1aHRqPmmhPjRr8b7h9fZoN/ah+fz0vbh1aHRqPmmhPjRr8b7h9fZoN/ah+fz0vbh1aHRqPmmhPjRr8b7h9fZoN/ah+fz0vbh1aHRqPmmhPjRr8b7h9fZoN/ah+fz0vbh1aHRqPmmhPjRr8b7by4mISsmRSQKQxYQW0dhd0xNRj41LCcORX9pOWosEB4PUhEYUFw1alEWAAwtPjZHRSwmBCUtRU9DVgIdRFFhN0AWOQ8gLjgeFWJ0YjE3RQ9pXAwSVlhhLBlYBRkoIj1LByMqKT86KRsEWBcYWVNpY2YWRk1hJDVLCycxNmIcDAEWUQ8CGWsjKw9dEx1obScDACxpMC8+EAANEAYfUz5hakwWMAQyODIHFmwWICspDgcTHiEDXlMpPgJTFR5hbXNLWGIFKy0iERsNV00zRV0mIhhYAx4yR3NLRWIfKzk/BB4QHjwTVlcqPxwYJQEuLjg/DC8sYmpqRVJeEC8YUFw1IwJRSC4tIjAAMSskJ0BqRVJDZgoCQlUtOUJpBAwiJiYbSwUlLSgrCSELUQceQEdhd0x6DwopOToFAmwOLiUoBB4wWAIVWEMyQEwWRk0XJCAeBC46bBUoBBEIRRNfcVsmDwJSRk1hbXNLRWJ0YgYjAhoXWQ0WGXIuLSlYAmdhbXNLMys6NysmFlw8UgISXEExZCpZAT41LCEfRWJpYmpqWFIvWQQZQ10vLUJwCQoSOTIZEUgsLC5AAwcNUxcYWFphHAVFEwwtPn0YADYPNyYmBwAKVwsFH0JoQEwWRk0XJCAeBC46bBk+BAYGHgUEW1gjOAVRDhlhcHMdXmIrIykhEAIvWQQZQ10vLUQfbE1hbXMCA2I/Yj4iABxDfAoWX0AoJAsYJB8oKjsfCyc6MWp3RUFYEC8YUFw1IwJRSC4tIjAAMSskJ2p3RUNXC0M9XlMpPgVYAUMGITwJBC4aKisuCgUQEF5RUVUtOQk8Rk1hbTYHFidDYmpqRVJDEEM9XlMpPgVYAUMDPzoMDTYnJzk5RU9DZgoCQlUtOUJpBAwiJiYbSwA7Ky0iERwGQxBRWEZhe2YWRk1hbXNLRQ4gJSI+DBwEHiAdWFcqHgVbA01hcHM9DDE8IyY5Sy0BUQAaQkRvCQBZBQYVJD4ORS07Ynt+b1JDEENRFxRhBgVRDhkoIzRFIi4mICsmNhoCVAwGRBR8ajpfFRggISBFOiAoISE/FVwkXAwTVlgSIg1SCRoybS1WRSQoLjkvb1JDEEMUWVBLLwJSbAs0IzAfDC0nYhwjFgcCXBBfRFE1BANwCQppO3phRWJpYhwjFgcCXBBfZEAgPgkYCAIHIjRLWGI/eWooBBEIRRM9XlMpPgVYAUVoR3NLRWIgJGo8RQYLVQ1Re10mIhhfCApvCzwMICwtYndqVBdVC0M9XlMpPgVYAUMHIjQ4ESM7Nmp3RUMGBmlRFxRhLwBFA00NJDQDESsnJWQMChUmXgdRChQXIx9DBwEyYwwJBCEiNzpkIx0EdQ0VF1szal0GVl16bR8CAio9KyQtSzQMVzAFVkY1alEWMAQyODIHFmwWICspDgcTHiUeUGc1Kx5CRgIzbWNLACwtSC8kAXhpHU5R1aHRqPmmhPjRr8b7h9fZoN/ah+fz0vbh1aHRqPmmhPjRr8b7h9fZoN/ah+fz0vbh1aHRqPmmhPjRr8b7h9fZoN/ah+fz0vbh1aHRqPmmhPjRr8b7h9fZoN/ah+fz0vbh1aHRqPmmhPjRr8b7h9fZoN/ah+fz0vbh1aHRqPmmhPjRr8b7h9fZoN/ah+fz0vbh1aHRqPmmhPjRr8b7h9fZoN/ah+fz0vbh1aHRqPmmhPjRr8b7h9fZoN/ah+fz0vbh1aHRqPmmhPjRr8b7h9fZoN/ah+fz0vbh1aHRqPmmhPjRR35GRXN7bGofLFKBsPdRW1sgLkx5BB4oKToKCxcgYmITVzlKEAIfUxQjPwVaAk01JTZLEisnJiU9b19OEIHkp9bU2o6j9o/U3bH+9aDc0qjf9ZD2oIHkp9bU2o6j9o/U3bH+9aDc0qjf9ZD2oIHkp9bU2o6j9o/U3bH+9aDc0qjf9ZD2oIHkp9bU2o6j9o/U3bH+9aDc0qjf9ZD2oIHkp9bU2o6j9o/U3bH+9aDc0qjf9ZD2oIHkp9bU2o6j9o/U3bH+9aDc0qjf9ZD2oIHkp9bU2o6j9o/U3bH+9aDc0qjf9ZD2oIHkp9bU2o6j9o/U3bH+9aDc0qjf9ZD2oIHkp9bU2o6j9o/U3bH+9aDc0qjf9ZD2oIHkp9bU2o6j9mcxPzoFEWphYBETVzk+EC8eVlAoJAsWKQ8yJDcCBCwcK2osCgBDFRBRGRpvaEUMAAIzIDIfTQEmLCwjAlwkcS40aHoABykfT2dLITwIBC5pDiMoFxMRSU9RY1wkJwl7BwMgKjYZSWIaIzwvKBMNUQQURT4tJQ9XCk0uJgYiRX9pMikrCR5LVhYfVEAoJQIeT2dhbXNLKSsrMCs4HFJDEENRFwlhJgNXAh41PzoFAmouIycvXzoXRBM2UkBpCQNYAAQmYwYiOhAMEgVqS1xDEi8YVUYgOBUYChggb3pCTWtDYmpqRSYLVQ4UelUvKwtTFE18bT8EBCY6NjgjCxVLVwIcUg4JPhhGIQg1ZRAECyQgJWQfLC0xdTM+Fxpvak5XAgkuIyBEMSosLy8HBBwCVwYDGVg0K04fT0VoR3NLRWIaIzwvKBMNUQQURRRhd0xaCQwlPicZDCwuai0rCBdZeBcFR3MkPkR1CQMnJDRFMAsWEA8aKlJNHkNTVlAlJQJFST4gOzYmBCwoJS84Sx4WUUFYHhxoQAlYAkRLJDVLCy09YiUhMDtDXxFRWVs1aiBfBB8gPypLESosLEBqRVJDRwIDWRxjETUELU0JODE2RQQoKyYvAVIXX0MdWFUlaiNUFQQlJDIFMCtnYgsoCgAXWQ0WGRZoQEwWRk0eCn0yVwkWBgsEISs8eDYzaHgOCyhzIk18bT0CCXlpMC8+EAANOgYfUz5LJgNVBwFhAiMfDC0nMWZqMR0EVw8URBR8aiBfBB8gPypFKjI9KyUkFl5DfAoTRVUzM0JiCQomITYYbw4gIDgrFwtNdgwDVFECIglVDQ8uNXNWRSQoLjkvb3gPXwAQWxQnPwJVEgQuI3MlCjYgJDNiERsXXAZdF1AkOQ8aRggzP3phRWJpYgYjBwACQhpLeVs1IwpPThZLbXNLRWJpYmoeDAYPVUNRFxRhakwLRggzP3MKCyZpamgPFwAMQkOTt5ZhaEwYSE01JCcHAGtpLThqERsXXAZdPRRhakwWRk1hCTYYBjAgMj4jChxDDUMVUkciagNERk9jYVlLRWJpYmpqRSYKXQZRFxRhakwWRlBheX9hRWJpYjdjbxcNVGl7W1siKwAWMQQvKTwcRX9pDiMoFxMRSVkyRVEgPglhDwMlIiRDHkhpYmpqMRsXXAZRFxRhakwWRk1hbXNWRWANIyQuHFUQEDQeRVglakzU5s9hbQpZLmIBNyhqRQRBEE1fF3cuJApfAUMSDgEiNRYWFA8YSXhDEENRcVsuPglERk1hbXNLRWJpYmp3RVA6AihRZFczIxxCRi8gLjhZJyMqKWpqh/LBEENTFxpvai9ZCAsoKn0sJA8MHQQLKDdPOkNRFxQPJRhfABQSJDcORWJpYmpqRU9DEjEYUFw1aEA8Rk1hbQADCjUKNzk+Ch8gRRECWEZhd0xCFBgkYVlLRWJpAS8kERcREENRFxRhakwWRk18bScZECdlSGpqRVIiRRceZFwuPUwWRk1hbXNLRX9pNjg/AF5pEENRF2YkOQVMBw8tKHNLRWJpYmpqWFIXQhYUGz5hakwWJQIzIzYZNyMtKz85RVJDEENMFwVxZmZLT2dLITwIBC5pFisoFlJeEBh7FxRhaj9DFBsoOzIHRX9pFSMkAR0UCiIVU2AgKEQUNRgzOzodBC5rbmpqRwELWQYdUxZoZmYWRk1hADIIDSsnJzlqWFI0WQ0VWEN7CwhSMgwjZXEmBCEhKyQvFlBPEENTQEYkJA9eRERtR3NLRWIANi8nFlJDEENMF2MoJAhZEVcAKTc/BCBhYAM+AB8QEk9RFxRhak5GBw4qLDQOR2tlSGpqRVIzXAIIUkZhakwLRjooIzcEEngIJi4eBBBLEjMdVk0kOE4aRk1hbXEeFic7YGNmb1JDEEM8XkciakwWRk18bQQCCyYmNXALARY3UQFZFXkoOQ8USk1hbXNLRWAgLCwlR1tPOkNRFxQCJQJQDwoybXNWRRUgLC4lEkgiVAclVlZpaC9ZCAsoKiBJSWJpYmguBAYCUgICUhZoZmYWRk1hHjYfESsnJTlqWFI0WQ0VWEN7CwhSMgwjZXE4ADY9KyQtFlBPEENTRFE1PgVYAR5jZH9hRWJpYgk4ABYKRBBRFwlhHQVYAgI2dxIPARYoIGJoJgAGVAoFRBZtakwWRAUkLCEfR2tlSDdAb19OEIHlt9bVyo6i5k0VDBFLVGKrwt5qNicxZiondnhhqPi2hPnBr8frh9bJoN7Kh+bj0vfx1aDBqPi2hPnBr8frh9bJoN7Kh+bj0vfx1aDBqPi2hPnBr8frh9bJoN7Kh+bj0vfx1aDBqPi2hPnBr8frh9bJoN7Kh+bj0vfx1aDBqPi2hPnBr8frh9bJoN7Kh+bj0vfx1aDBqPi2hPnBr8frh9bJoN7Kh+bj0vfx1aDBqPi2hPnBr8frh9bJoN7Kh+bjOg8eVFUtaj9DFDkjNR9LWGIdIyg5SyEWQhUYQVUtcC1SAiEkKyc/BCArLTJiTHgPXwAQWxQSPx5iEQQyOTYPRX9pET84MRAbfFkwU1AVKw4eRDk2JCAfACZpBxkaR1tpXAwSVlhhGRlEKAI1JDUSRWJ0Yhk/FyYBSC9LdlAlHg1UTk8PIicCAyssMGhjb3gwRRElQF0yPglSXCwlKR8KByclajFqMRcbRENMFxYJIwteCgQmJScYRSc/JzgzRSYUWRAFUlBhHgNZCE0oI3MfDSdpIT84FxcNREMDWFssahtfEgVhIzIGAGJiYi4jFgYCXgAUGRZtaihZAx4WPzIbRX9pNjg/AFIeGWkiQkYVPQVFEggldxIPAQYgNCMuAABLGWkiQkYVPQVFEggldxIPARYmJS0mAFpBdTAhY0MoORhTAk9tbShLMScxNmp3RVA3RwoCQ1ElaillNk9tbRcOAyM8Lj5qWFIFUQ8CUhhhCQ1aCg8gLjhLWGIMERpkFhcXZBQYREAkLkxLT2cSOCE/Eis6Ni8uXzMHVDceUFMtL0QUIz4RGSQCFjYsJg4jFgZBHEMKF2AkMhgWW01jHjsEEmItKzk+BBwAVUFdF3AkLA1DChlhcHMfFzcsbkBqRVJDcwIdW1YgKQcWW00nOD0IESsmLGI8TFImYzNfZEAgPgkYEhooPicOAQYgMT4rCxEGEF5RQRQkJAgWG0RLHiYZMTUgMT4vAUgiVAclWFMmJgkeRCgSHQADCjUGLCYzJh4MQwZTGxQ6ajhTHhlhcHNJLSstJ2ojA1IXXwxRUVUzaEAWIggnLCYHEWJ0YiwrCQEGHGlRFxRhHgNZChkoPXNWRWAGLCYzRQAGXgcURRQEGTwWAAIzbTYFESs9Ky85RQUKRAsYWRQCJgNFA00TLD0MAGxrbkBqRVJDcwIdW1YgKQcWW00nOD0IESsmLGI8TFImYzNfZEAgPgkYFQUuOhwFCTsKLiU5AFJeEBVRUlolahEfbD40PwccDDE9Jy5wJBYHYw8YU1EzYk5zNT0CITwYABAoLC0vR15DS0MlUkw1alEWRC4tIiAORTAoLC0vR15DdAYXVkEtPkwLRltxYXMmDCxpf2p4VV5DfQIJFwlheFwGSk0TIiYFASsnJWp3RUJPEDAEUVIoMkwLRk9hPidJSUhpYmpqJhMPXAEQVF9hd0xQEwMiOToEC2o/a2oPNiJNYxcQQ1FvKQBZFQgTLD0MAGJ0YjxqABwHEB5YPWc0ODhBDx41KDdRJCYtDisoAB5LEjcGXkc1LwgWBQItIiFJTHgIJi4JCh4MQjMYVF8kOEQUIz4RGSQCFjYsJgklCR0REk9RTD5hakwWIggnLCYHEWJ0Yg8ZNVwwRAIFUho1PQVFEgglDjwHCjBlYh4jER4GEF5RFWA2Ix9CAwlhCAA7RSEmLiU4R15pEENRF3cgJgBUBw4qbW5LAzcnIT4jChxLU0pRcmcRZD9CBxkkYyccDDE9Jy4JCh4MQkNMF1dhLwJSRhBoR1k4EDAHLT4jAwtZcQcVe1UjLwAeHU0VKCsfRX9pYBolFQFDUUMDUlBhKA1YCAgzbT0OBDBpNiIvRQYMQEMeURQ4JRlERh4iPzYOC2I+Ki8kRRNDZBQYREAkLkxTCBkkPyBLFTAmOiMnDAYaHkFdF3AuLx9hFAwxbW5LETA8J2o3THgwRRE/WEAoLBUMJwklCTodDCYsMGJjbyEWQi0eQ10nM1Z3AgkVIjQMCSdhYAQlERsFWQYDFRhhMUxiAxU1bW5LRxY+Kzk+ABZDYBEeT10sIxhPRiMuOToNDCc7YGZqIRcFURYdQxR8agpXCh4kYXMoBC4lICspDlJeEDAERUIoPA1aSB4kOR0EESsvKy84RQ9KOjAERXouPgVQH1cAKTc4CSstJzhiRzwMRAoXXlEzGA1YAQhjYXMQRRYsOj5qWFJBZBEYUFMkOExEBwMmKHFHRQYsJCs/CQZDDUNCAhhhBwVYRlBhfGNHRQ8oOmp3RUNRAE9RZVs0JAhfCAphcHNbSWIaNywsDApDDUNTF0c1aEA8Rk1hbRAKCS4rIykhRU9DVhYfVEAoJQIeEERhHiYZEys/IyZkNgYCRAZfWVs1IwpfAx8TLD0MAGJ0YjxqABwHEB5YPT4tJQ9XCk0SOCE/BzobYndqMRMBQ00iQkY3IxpXClcAKTc5DCUhNh4rBxAMSEtYPVguKQ1aRj40PxIFESsOMCsoRU9DYxYDY1Y5GFZ3AgkVLDFDRwMnNiNnIgACUkFYPVguKQ1aRj40PxAEASc6YmpqRU9DYxYDY1Y5GFZ3AgkVLDFDRwEmJi85R1tpOjAERXUvPgVxFAwjdxIPAQ4oIC8mTQlDZAYJQxR8ak53ExkuIDIfDCEoLiYzRQESRQoDWhkiKwJVAwEybSQDACxpI2oeEhsQRAYVF1MzKw5FRhQuOH1LNjc7NCM8BB5DXAoXUkcgPAlESE9tbRcEADEeMCs6RU9DRBEEUhQ8Y2ZlEx8AIycCIjAoIHALARYnWRUYU1EzYkU8NRgzDD0fDAU7IyhwJBYHZAwWUFgkYk53CBkoCiEKB2BlYjFqMRcbRENMFxYAPxhZRj4wODoZCG8KIyQpAB5DXw1RUEYgKE4aRikkKzIeCTZpf2osBB4QVU97FxRhajhZCQE1JCNLWGJrBCM4AAFDRAsUF2cwPwVECywjJD8CETsKIyQpAB5DQgYcWEAkahheA00sIj4OCzZpOyU/RRUGREMWRVUjKAlSSE9tR3NLRWIKIyYmBxMAW0NMF2c0OBpfEAwtYyAOEQMnNiMNFxMBEB5YPT4SPx51CQkkPmkqASYFIygvCVoYEDcUT0Bhd0wUNAglKDYGRSsnby0rCBdDUwwVUkdvai5DDwE1YDoFRS4gMT5qFxcFQgYCX1EyagNVBQwyJDwFBC4lO2RoSVInXwYCYEYgOkwLRhkzODZLGGtDET84Jh0HVRBLdlAlDgVADwkkP3tCbxE8MAklARcQCiIVU3Y0PhhZCEU6bQcOHTZpf2poNxcHVQYcF3UNBkxUEwQtOX4CC2IqLS4vFlBPECUEWVdhd0xQEwMiOToEC2pgSGpqRVIFXxFRaBhhKQNSA00oI3MCFSMgMDliJh0NVgoWGXcODillT00lIllLRWJpYmpqRSAGXQwFUkdvIwJACQYkZXEoCiYsBzwvCwZBHEMSWFAkY2YWRk1hbXNLRTYoMSFkEhMKREtBGQBoQEwWRk0kIzdhRWJpYgQlERsFSUtTdFslLx8USk1jGSECACZpYGpkS1JAcwwfUV0mZC95IigSbX1FRWBpISUuAAFNEkp7UlolahEfbD40PxAEASc6eAsuATsNQBYFHxYCPx9CCQACIjcOR25pOWoeAAoXEF5RFXc0ORhZC00iIjcOR25pBi8sBAcPRENMFxZjZkxmCgwiKDsECSYsMGp3RVAAXwcUF1wkOAkUSk0CLD8HByMqKWp3RRQWXgAFXlsvYkUWAwMlbS5CbxE8MAklARcQCiIVU3Y0PhhZCEU6bQcOHTZpf2poNxcHVQYcF1c0ORhZC00iIjcOR25pBD8kBlJeEAUEWVc1IwNYTkRLbXNLRS4mISsmRREMVAZRChQOOhhfCQMyYxAeFjYmLwklARdDUQ0VF3sxPgVZCB5vDiYYES0kASUuAFw1UQ8EUhQuOEwURGdhbXNLDCRpISUuAFJeDUNTFRQ1IglYRiMuOToNHGprASUuAFBPEEE0WkQ1M04aRhkzODZCXmI7Jz4/FxxDVQ0VPRRhakxkAwAuOTYYSysnNCUhAFpBcwwVUnE3LwJCREFhLjwPAGtyYgQlERsFSUtTdFslL04aRk8VPzoOAXhpYGpkS1IAXwcUHj4kJAgWG0RLR35GRaDdwqje5ZD3sEMldnZheEzU5vlhABIoLQsHBxlqh+bj0vfx1aDBqPi2hPnBr8frh9bJoN7Kh+bj0vfx1aDBqPi2hPnBr8frh9bJoN7Kh+bj0vfx1aDBqPi2hPnBr8frh9bJoN7Kh+bj0vfx1aDBqPi2hPnBr8frh9bJoN7Kh+bj0vfx1aDBqPi2hPnBr8frh9bJoN7Kh+bj0vfx1aDBqPi2hPnBr8frh9bJoN7Kh+bj0vfx1aDBqPi2hPnBr8frby4mISsmRT8CUws9FwlhHg1UFUMMLDADDCwsMXALARYvVQUFcEYuPxxUCRVpbx4KBiogLC9qICEzEk9RFUMzLwJVDk9oRx4KBioFeAsuAT4CUgYdH09hHglOEk18bXEjDCUhLiMtDQYQEAYHUkY4agFXBQUoIzZLEis9KmojEQFDUwwcR1gkPgVZCE1kY3FHRQYmJzkdFxMTEF5RQ0Y0L0xLT2cMLDADKXgIJi4ODAQKVAYDHx1LBw1VDiF7DDcPMS0uJSYvTVAmYzM8VlcpIwJTREFhNnM/ADo9YndqRz8CUwsYWVFhDz9mREFhCTYNBDclNmp3RRQCXBAUGxQCKwBaBAwiJnNWRQcaEmQ5AAYuUQAZXlokahEfbCAgLjsnXwMtJgYrBxcPGEE8VlcpIwJTRg4uITwZR2tzAy4uJh0PXxEhXlcqLx4eRCgSHR4KBiogLC8JCh4MQkFdF09LakwWRikkKzIeCTZpf2oPNiJNYxcQQ1FvJw1VDgQvKBAECS07bmoeDAYPVUNMFxYMKw9eDwMkbRY4NWIqLSYlF1BPOkNRFxQCKwBaBAwiJnNWRSQ8LCk+DB0NGABYF3ESGkJlEgw1KH0GBCEhKyQvJh0PXxFRChQiaglYAk08ZFlhCS0qIyZqKBMAWDFRChQVKw5FSCAgLjsCCyc6eAsuASAKVwsFcEYuPxxUCRVpbxIeES1pMSEjCR5DUwsUVF9jZkwUDQg4b3phKCMqKhhwJBYHfAITUlhpMUxiAxU1bW5LRxAsIy45RQYLVUMCUkY3Lx4RFU01LCEMADZpJDglCFIXWAZRRF8oJgAbBQUkLjhLBDAuMWorCxZDQgYFQkYvOUxfEkNhGjIfBiotLS1qFxdOWQ0CQ1UtJh8WDwthOTsORSUoLy9qFxcQVRcCF101ZE4aRikuKCA8FyM5YndqEQAWVUMMHj4MKw9eNFcAKTcvDDQgJi84TVtpfQISX2Z7CwhSMgImKj8OTWAINz4lNhkKXA8yX1EiIU4aRhZhGTYTEWJ0YmgLEAYMEDAaXlgtai9eAw4qb39LIScvIz8mEVJeEAUQW0ckZmYWRk1hGTwECTYgMmp3RVAiRRceGkQgOR9TFU0iJCEICSdpIyQuRQYRVQIVWl0tJkxFDQQtIXMIDScqKTlqBwtDQgYFQkYvIwJRRhkpKHMYADA/JzhtFlIMRw1RQ1UzLQlCRhsgISYOS2BlSGpqRVIgUQ8dVVUiIUwLRiAgLjsCCydnMS8+JAcXXzAaXlgtKQRTBQZhMHphKCMqKhhwJBYHYw8YU1EzYk5wBwEtLzIIDhQoLj8vR15DS0MlUkw1alEWRCsgIT8JBCEiYjwrCQcGEEsYURQvJUxCBx8mKCdLDCxpIzgtFltBHEM1UlIgPwBCRlBhfX1eSWIEKyRqWFJTHlNdF3kgMkwLRlxvfX9LNy08LC4jCxVDDUNDGz5hakwWMgIuIScCFWJ0YmgFCx4aEBYCUlBhIwoWEQhhLjIFQjZpIz8+Cl8HVRcUVEBhPgRTRhkgPzQOEWxpFjgzRUJNA0NeFwRvf0wZRl1venMCA2IgNmonDAEQVRBfFRhLakwWRi4gIT8JBCEiYndqAwcNUxcYWFppPEUWKwwiJToFAGwaNis+AFwFUQ8dVVUiITpXChgkbW5LE2IsLC5qGFtpfQISX2Z7CwhSNQEoKTYZTWAaKSMmCTELVQAac1EtKxUUSk06bQcOHTZpf2poNxcQQAwfRFFhLglaBxRjYXMvACQoNyY+RU9DAE9Rel0valEWVkNxYXMmBDppf2p7S0dPEDEeQlolIwJRRlBhf39LNjcvJCMyRU9DEkMCFRhLakwWRjkuIj8fDDJpf2poNRMWQwZRVVEnJR5TRgwvPiQOFysnJWRqVVJeEAofREAgJBgYREFLbXNLRQEoLiYoBBEIEF5RUUEvKRhfCQNpO3pLKCMqKiMkAFwwRAIFUhogPxhZNQYoIT8IDScqKQ4vCRMaEF5RQRQkJAgWG0RLADIIDRBzAy4uIRsVWQcURRxoQCFXBQUTdxIPARYmJS0mAFpBdAYTQlMSIQVaCi4pKDAAR25pOWoeAAoXEF5RFcTe2vcWIggjODRRRTI7KyQ+RRMRVxBRQ1thKQNYFQItKHFHRQYsJCs/CQZDDUMXVlgyL0A8Rk1hbQcECi49KzpqWFJBYBEYWUAyahheA00yJjoHCW8qKi8pDlICQgQCFxwxOAlFFU0HdHMfCmI6Jy9jS1I2QwZRQ1woOUxZCA4kbScERS4sIzgkRQYLVUMFVkYmLxgWAAQkITdLCyMkJ2ZqERoGXkMFQkYvagNQAENjYVlLRWJpASsmCRACUwhRChQMKw9eDwMkYyAOEQYsID8tNQAKXhdRSh1LBw1VDj97DDcPJzc9NiUkTQlDZAYJQxR8ak5kA0AoIyAfBC4lYiIlChlDXgwGFRhLakwWRjkuIj8fDDJpf2poIx0RUwZRRVFsKxxGChRhJDVLDDZpMT4lFQIGVEMGWEYqIwJRRgwnOTYZRSNpMC85FRMUXk1TGz5hakwWIBgvLnNWRSQ8LCk+DB0NGEp7FxRhakwWRk0MLDADDCwsbDkvETMWRAwiXF0tJg9eAw4qZTUKCTEsa3FqERMQW00GVl01YlwYVlhodnMmBCEhKyQvSwEGRCIEQ1sSIQVaCg4pKDAATTY7Ny9jb1JDEENRFxRhBANCDws4ZXE4DislLmoJDRcAW0FdFxYTL0FeCQIqKDdFR2tDYmpqRRcNVEMMHj5LZ0EWhPnBr8frh9bJYh4LJ1JQEIHxoxQIHil7NU2j2dOJ8cKr1sqo8fKBpOOTo7Sj3uzU8u2j2dOJ8cKr1sqo8fKBpOOTo7Sj3uzU8u2j2dOJ8cKr1sqo8fKBpOOTo7Sj3uzU8u2j2dOJ8cKr1sqo8fKBpOOTo7Sj3uzU8u2j2dOJ8cKr1sqo8fKBpOOTo7Sj3uzU8u2j2dOJ8cKr1sqo8fKBpOOTo7Sj3uzU8u2j2dOJ8cKr1sqo8fKBpOOTo7Sj3uzU8u2j2dNhCS0qIyZqLAYOfENMF2AgKB8YLxkkICBRJCYtDi8sETURXxYBVVs5Yk5/EggsbRY4NWBlYmg6BBEIUQQUFR1LAxhbKlcAKTcnBCAsLmIxRSYGSBdRChRjAgVRDgEoKjsfFmIsNC84HFITWQAaVlYtL0xfEggsbToFRTYhJ2opEAARVQ0FF0YuJQEYREFhCTwOFhU7IzpqWFIXQhYUF0loQCVCCyF7DDcPISs/Ky4vF1pKOioFWnh7CwhSMgImKj8OTWAMERoDERcOEk9RTBQVLxRCRlBhbxofAC9pBxkaR15DdAYXVkEtPkwLRgsgISAOSWIKIyYmBxMAW0NMF3ESGkJFAxkIOTYGRT9gSAM+CD5ZcQcVe1UjLwAeRCQ1KD5LBi0lLThoTEgiVAcyWFguODxfBQYkP3tJIBEZCz4vCDEMXAwDFRhhMWYWRk1hCTYNBDclNmp3RTcwYE0iQ1U1L0JfEggsDjwHCjBlYh4jER4GEF5RFX01LwEWIz4RbTAECS07YGZARVJDECAQW1gjKw9dRlBhKyYFBjYgLSRiBltDdTAhGWc1KxhTSAQ1KD4oCi4mMGp3RRFDVQ0VF0loQGZaCQ4gIXMiES8bYndqMRMBQ004Q1EsOVZ3AgkTJDQDEQU7LT86Bx0bGEEwQkAuahxfBQY0PXFHRWA6IzwvR1tpeRccZQ4ALgh6Bw8kIXsQRRYsOj5qWFJBZwIdXEdhPgMWCAggPzESRSs9Jyc5RRMNVEMWRVUjOUxCDggsY3M5BCwuJ2ojFlIAXw0CUkY3KxhfEAhhLypLAScvIz8mEVxBHEM1WFEyHR5XFk18bScZECdpP2NALAYOYlkwU1AFIxpfAggzZXphLDYkEHALARY3XwQWW1FpaC1DEgIRJDAAEDJrbmoxRSYGSBdRChRjCxlCCU0RJDAAEDJpLC8rFxAaEAoFUlkyaEAWIggnLCYHEWJ0YiwrCQEGHGlRFxRhCQ1aCg8gLjhLWGIvNyQpERsMXksHHhQoLExARhkpKD1LJDc9LRojBhkWQE0CQ1UzPkQfRggtPjZLJDc9LRojBhkWQE0CQ1sxYkUWAwMlbTYFAWI0a0ADER8xCiIVU2ctIwhTFEVjHToIDjc5ECskAhdBHEMKF2AkMhgWW01jHToIDjc5YjgrCxUGEk9Rc1EnKxlaEk18bWJZSWIEKyRqWFJWHEM8Vkxhd0wOVkFhHzweCyYgLC1qWFJTHEMiQlInIxQWW01jbSAfR25DYmpqRTECXA8TVlcqalEWABgvLicCCixhNGNqJAcXXzMYVF80OkJlEgw1KH0ZBCwuJ2p3RQRDVQ0VF0loQCVCCz97DDcPNi4gJi84TVAzWQAaQkQIJBhTFBsgIXFHRTlpFi8yEVJeEEEyX1EiIUxfCBkkPyUKCWBlYg4vAxMWXBdRChRxZFkaRiAoI3NWRXJncGZqKBMbEF5RAhhhGANDCAkoIzRLWGJ7bmoZEBQFWRtRChRjah8USmdhbXNLJiMlLigrBhlDDUMXQloiPgVZCEU3ZHMqEDYmEiMpDgcTHjAFVkAkZAVYEggzOzIHRX9pNGovCxZDTUp7PRlsao6i5o/VzbH/5WIdAwhqUVKBsPdRZ3gAEylkRo/VzbH/5aDdwqje5ZD3sIHlt9bVyo6i5o/VzbH/5aDdwqje5ZD3sIHlt9bVyo6i5o/VzbH/5aDdwqje5ZD3sIHlt9bVyo6i5o/VzbH/5aDdwqje5ZD3sIHlt9bVyo6i5o/VzbH/5aDdwqje5ZD3sIHlt9bVyo6i5o/VzbH/5aDdwqje5ZD3sIHlt9bVyo6i5o/VzbH/5aDdwqje5ZD3sIHlt9bVyo6i5mctIjAKCWIZLjgeBwovEF5RY1UjOUJmCgw4KCFRJCYtDi8sESYCUgEeTxxoQABZBQwtbR4EEycdIyhqWFIzXBElVUwNcC1SAjkgL3tJKC0/JycvCwZBGWkdWFcgJkxgDx4VLDFLRX9pEiY4MRAbfFkwU1AVKw4eRDsoPiYKCTFra0BAKB0VVTcQVQ4ALgh6Bw8kIXsQRRYsOj5qWFJB0vnRF3MgJwkWDgwybTJLFic7NC84SAEKVAZRREQkLwgWBQUkLjhFRQYsJCs/CQYQEBAFVk1hPwJSAx9hOTsORTYhMC85DR0PVE1TGxQFJQlFMR8gPXNWRTY7Ny9qGFtpfQwHUmAgKFZ3AgkFJCUCASc7amNAKB0VVTcQVQ4ALghlCgQlKCFDRxUoLiEZFRcGVEFdF09hHglOEk18bXE8BC4iYhk6ABcHEk9Rc1EnKxlaEk18bWJeSWIEKyRqWFJSBU9RelU5alEWVF9tbQEEECwtKyQtRU9DAE9RZEEnLAVORlBhb3MYETctMWU5R15pEENRF2AuJQBCDx1hcHNJNiMvJ2o4BBwEVUMYRBQ0OkxCCU1jbX1FRQEmLCwjAlwwcSU0aHkAEjNlNigECXNFS2JrbGoNBB8GEAcUUVU0JhgWDx5hfGZFR25DYmpqRTECXA8TVlcqalEWKwI3KD4OCzZnMS8+MhMPWzABUlElahEfbCAuOzY/BCBzAy4uMR0EVw8UHxYDMxxXFR4SPTYOAQEoMmhmRQlDZAYJQxR8ak53CgEuOnMZDDEiO2o5FRcGVBBRHwpzeEUUSk0FKDUKEC49YndqAxMPQwZdF2YoOQdPRlBhOSEeAG5DYmpqRSYMXw8FXkRhd0wUMwMtIjAAFmI9Ki9qFh4KVAYDF1UjJRpTRl9zY3MmBDtpNjgjAhUGQkMCR1EkLkxQCgwmY3FHb2JpYmoJBB4PUgISXBR8agpDCA41JDwFTTRgSGpqRVJDEENRels3LwFTCBlvHicKESdnIDM6BAEQYxMUUlACKxwWW003R3NLRWJpYmpqDBRDfxMFXlsvOUJhBwEqHiMOACZpIyQuRT0TRAoeWUdvHQ1aDT4xKDYPSw8oOmo+DRcNOkNRFxRhakwWRk1hbX5GRQ0rMSMuDBMNZQpRU1skOQIREk0kNSMEFidpJjMkBB8KU0MCW10lLx4WCww5dnMeFic7Yic/FgZDQgZcRFE1ahpXChgkbT4KCzcoLiYzb1JDEENRFxRhLwJSbE1hbXMOCyZpP2NAKB0VVTcQVQ4ALghlCgQlKCFDRwg8LzoaCgUGQkFdF09hHglOEk18bXEhEC85YholEhcREk9Rc1EnKxlaEk18bWZbSWIEKyRqWFJWAE9RelU5alEWVF1xYXM5CjcnJiMkAlJeEFNdF3cgJgBUBw4qbW5LKC0/JycvCwZNQwYFfUEsOjxZEQgzbS5Cbw8mNC8eBBBZcQcVY1smLQBTTk8IIzUhEC85YGZqHlI3VRsFFwlhaCVYAAQvJCcORQg8LzpoSVInVQUQQlg1alEWAAwtPjZHRQEoLiYoBBEIEF5Rels3LwFTCBlvPjYfLCwvCD8nFVIeGWk8WEIkHg1UXCwlKQcEAiUlJ2JoKx0AXAoBFRhhahcWMgg5OXNWRWAHLSkmDAJBHENRFxRhakwWIggnLCYHEWJ0YiwrCQEGHEMyVlgtKA1VDU18bR4EEyckJyQ+SwEGRC0eVFgoOkxLT2cMIiUOMSMreAsuATYKRgoVUkZpY2Z7CRskGTIJXwMtJh4lAhUPVUtTcVg4aEAWHU0VKCsfRX9pYAwmHFBPECcUUVU0JhgWW00nLD8YAG5pECM5DgtDDUMFRUEkZmYWRk1hGTwECTYgMmp3RVAvWQgUW01hPgMWEh8oKjQOF2IoLD4jSBELVQIFF10nahlFAwlhLjIZAC4sMTkmHFxBHGlRFxRhCQ1aCg8gLjhLWGIELTwvCBcNRE0CUkAHJhUWG0RLADwdABYoIHALARYwXAoVUkZpaCpaHz4xKDYPR25pOWoeAAoXEF5RFXItM0xFFggkKXFHRQYsJCs/CQZDDUNEBxhhBwVYRlBhfGNHRQ8oOmp3RUBTAE9RZVs0JAhfCAphcHNbSWIKIyYmBxMAW0NMF3kuPAlbAwM1YyAOEQQlOxk6ABcHEB5YPXkuPAliBw97DDcPISs/Ky4vF1pKOi4eQVEVKw4MJwklGTwMAi4samgLCwYKcSU6FRhhMUxiAxU1bW5LRwMnNiNnJDQoEk9Rc1EnKxlaEk18bScZECdlSGpqRVI3XwwdQ10xalEWRC8tIjAAFmI9Ki9qV0JOXQofQkAkagVSCghhJjoIDmxrbmoJBB4PUgISXBR8aiFZEAgsKD0fSzEsNgskERsidihRSh1LBwNAAwAkIydFFic9AyQ+DDMle0sFRUEkY2Z7CRskGTIJXwMtJg4jExsHVRFZHj4MJRpTMgwjdxIPAQA8Nj4lC1oYEDcUT0Bhd0wUNQw3KHMIEDA7JyQ+RQIMQwoFXlsvaEAWIBgvLnNWRSQ8LCk+DB0NGEpRXlJhBwNAAwAkIydFFiM/JxolFlpKEBcZUlphBANCDws4ZXE7CjFrbmgZBAQGVE1THhQkJh9TRiMuOToNHGprEiU5R15BfgxRVFwgOE4aEh80KHpLACwtYi8kAVIeGWk8WEIkHg1UXCwlKREeETYmLGIxRSYGSBdRChRjGAlVBwEtbSAKEyctYjolFhsXWQwfFRhhDBlYBU18bTUeCyE9KyUkTVtDWQVRels3LwFTCBlvPzYIBC4lEiU5TVtDRAsUWRQPJRhfABRpbwMEFmBlYBgvBhMPXAYVGRZoaglaFQhhAzwfDCQwamgaCgFBHEE/WEApIwJRRh4gOzYPR249MD8vTFIGXgdRUlolahEfbGcXJCA/BCBzAy4uKRMBVQ9ZTBQVLxRCRlBhbwQEFy4tYiYjAhoXWQ0WFx9hOgBXHwgzbRY4NWxrbmoOChcQZxEQRxR8ahhEEwhhMHphMys6FisoXzMHVCcYQV0lLx4eT2cXJCA/BCBzAy4uMR0EVw8UHxYHPwBaBB8oKjsfR25pOWoeAAoXEF5RFXI0JgBUFAQmJSdJSWINJywrEB4XEF5RUVUtOQkaRi4gIT8JBCEiYndqMxsQRQIdRBoyLxhwEwEtLyECAio9YjdjbyQKQzcQVQ4ALghiCQomITZDRwwmBCUtR15DEENRFxQ6ajhTHhlhcHNJNyckLTwvRRQMV0FdF3AkLA1DChlhcHMNBC46J2ZqJhMPXAEQVF9hd0xgDx40LD8YSzEsNgQlIx0EEB5YPWIoOThXBFcAKTcvDDQgJi84TVtpZgoCY1UjcC1SAjkuKjQHAGprBxkaNR4CSQYDFRhhahcWMgg5OXNWRWAZLiszAABDdTAhFRhhDglQBxgtOXNWRSQoLjkvSVIgUQ8dVVUiIUwLRigSHX0YADYZLiszAABDTUp7YV0yHg1UXCwlKR8KByclamgaCRMaVRFRVFstJR4UT1cAKTcoCi4mMBojBhkGQktTcmcRGgBXHwgzDjwHCjBrbmoxb1JDEEM1UlIgPwBCRlBhCAA7SxE9Iz4vSwIPURoURXcuJgNESk0VJCcHAGJ0YmgaCRMaVRFRcmcRag9ZCgIzb39hRWJpYgkrCR4BUQAaFwlhLBlYBRkoIj1DBmtpBxkaSyEXURcUGUQtKxVTFC4uITwZRX9pIWovCxZDTUp7PVguKQ1aRj0tPwcJHRBpf2oeBBAQHjMdVk0kOFZ3AgkTJDQDERYoICglHVpKOg8eVFUtajhGNAIuIHNWRRIlMB4oHSBZcQcVY1UjYk5kCQIsbQc7FmBgSCYlBhMPEDcBZ1gzOUwLRj0tPwcJHRBzAy4uMRMBGEEhW1U4Lx4WMj1jZFlhMTIbLSUnXzMHVC8QVVEtYhcWMgg5OXNWRWAdJyYvFR0RREMQRVs0JAgWEgUkbTAeFzAsLD5qFx0MXU1TGxQFJQlFMR8gPXNWRTY7Ny9qGFtpZBMjWFsscC1SAikoOzoPADBha0AeFSAMXw5LdlAlCBlCEgIvZShLMScxNmp3RVCBtvFRclgkPA1CCR9jYXMtECwqYndqAwcNUxcYWFppY2YWRk1hITwIBC5pMmp3RSAMXw5fUFE1DwBTEAw1IiE7CjFha0BqRVJDWQVRRxQ1IglYRjg1JD8YSzYsLi86CgAXGBNRHBQXLw9CCR9yYz0OEmp5bn5mVVtKC0M/WEAoLBUeRDkRb39Jh8TbYg8mAAQCRAwDFR1LakwWRggtPjZLKy09KywzTVA3YEFdFXouaglaAxsgOTwZR249MD8vTFIGXgd7UlolahEfbDkxHzwECHgIJi4IEAYXXw1ZTBQVLxRCRlBhb7Ht92IHJys4AAEXEA4QVFwoJAkUSk0HOD0IRX9pJD8kBgYKXw1ZHj5hakwWCgIiLD9LOm5pKjg6RU9DZRcYW0dvLAVYAiA4GTwEC2pgSGpqRVIKVkMfWEBhIh5GRhkpKD1LKy09KywzTVA3YEFdFXouag9eBx9jYScZECdgeWo4AAYWQg1RUlolQEwWRk0tIjAKCWIrJzk+SVIBVENMF1ooJkAWCww1JX0DECUsSGpqRVIFXxFRaBhhJ0xfCE0oPTICFzFhECUlCFwEVRc8VlcpIwJTFUVoZHMPCkhpYmpqRVJDEA8eVFUtaggWW00UOToHFmwtKzk+BBwAVUsZRURvGgNFDxkoIj1HRS9nMCUlEVwzXxAYQ10uJEU8Rk1hbXNLRWIgJGouRU5DUgdRQ1wkJExUAk18bTdQRSAsMT5qWFIOEAYfUz5hakwWAwMlR3NLRWIgJGooAAEXEBcZUlphHxhfCh5vOTYHADImMD5iBxcQRE0DWFs1ZDxZFQQ1JDwFRWlpFC8pER0RA00fUkNpekACSl1oZGhLKy09KywzTVA3YEFdFdbH2EwUSEMjKCAfSywoLy9jb1JDEEMUW0ckaiJZEgQnNHtJMRJrbmgEClIOUQAZXlokaEBCFBgkZHMOCyZDJyQuRQ9KOjcBZVsuJ1Z3AgkDOCcfCixhOWoeAAoXEF5RFdbH2Ex4AwwzKCAfRSs9JydoSVIlRQ0SFwlhLBlYBRkoIj1DTEhpYmpqCR0AUQ9RaBhhIh5GRlBhGCcCCTFnJCMkAT8aZAweWRxoQEwWRk0oK3MFCjZpKjg6RQYLVQ1ReVs1IwpPTk8VHXFHRwwmYikiBABBHBcDQlFocUxEAxk0Pz1LACwtSGpqRVIPXwAQWxQjLx9CSk0jKXNWRSwgLmZqCBMXWE0ZQlMkQEwWRk0nIiFLOm5pK2ojC1IKQAIYRUdpGANZC0MmKCciESckMWJjTFIHX2lRFxRhakwWRgEuLjIHRSZpf2ofERsPQ00VXkc1KwJVA0UpPyNFNS06Kz4jChxPEApfRVsuPkJmCR4oOToEC2tDYmpqRVJDEEMYURQlalAWBAlhOTsOC2IrJmp3RRZYEAEUREBhd0xfRggvKVlLRWJpJyQub1JDEEMYURQjLx9CRhkpKD1LMDYgLjlkERcPVRMeRUBpKAlFEkMzIjwfSxImMSM+DB0NEEhRYVEiPgNEVUMvKCRDVW56bnpjTElDfgwFXlI4Yk5iNk9tb7Ht92JrbGQoAAEXHg0QWlFoQEwWRk0kISAORQwmNiMsHFpBZDNTGxYPJUxfEggsPnFHETA8J2NqABwHOgYfUxQ8Y2Y8CgIiLD9LAzcnIT4jChxDVwYFZ1ggMwlEKAwsKCBDTEhpYmpqCR0AUQ9RWEE1alEWHRBLbXNLRSQmMGoVSVITEAofF10xKwVEFUURITISADA6eA0vESIPURoURUdpY0UWAgJLbXNLRWJpYmojA1ITEB1MF3guKQ1aNgEgNDYZRTYhJyRqERMBXAZfXloyLx5CTgI0OX9LFWwHIycvTFIGXgd7FxRhaglYAmdhbXNLDCRpYSU/EVJeDUNBF0ApLwIWEgwjITZFDCw6Jzg+TR0WRE9RFRwvJQJTT09obTYFAUhpYmpqFxcXRREfF1s0PmZTCAlLGSM7CTA6eAsuAT4CUgYdH09hHglOEk18bXE/AC4sMiU4EVIXX0MQWVs1IglERh0tLCoOF2IgLGo+DRdDQwYDQVEzZE4aRikuKCA8FyM5YndqEQAWVUMMHj4VOjxaFB57DDcPISs/Ky4vF1pKOjcBZ1gzOVZ3AgkFPzwbAS0+LGJoMQIzXAIIUkZjZkxNRjkkNSdLWGJrEiYrHBcREk9RYVUtPwlFRlBhKjYfNS4oOy84KxMOVRBZHhhhDglQBxgtOXNWRWBhLCUkAFtBHEMyVlgtKA1VDU18bTUeCyE9KyUkTVtDVQ0VF0loQDhGNgEzPmkqASYLNz4+ChxLS0MlUkw1alEWRD8kKyEOFippLiM5EVBPECUEWVdhd0xQEwMiOToEC2pgSGpqRVIKVkM+R0AoJQJFSDkxHT8KHCc7YiskAVIsQBcYWFoyZDhGNgEgNDYZSxEsNhwrCQcGQ0MFX1EvaiNGEgQuIyBFMTIZLiszAABZYwYFYVUtPwlFTgokOQMHBDssMAQrCBcQGEpYF1EvLmZTCAlhMHphMTIZLjg5XzMHVCEEQ0AuJERNRjkkNSdLWGJrFi8mAAIMQhdRQ1thOQlaAw41KDdJSWIPNyQpRU9DVhYfVEAoJQIeT2dhbXNLCS0qIyZqC1JeECwBQ10uJB8YMh0RITISADBpIyQuRT0TRAoeWUdvHhxmCgw4KCFFMyMlNy9ARVJDEE5cF3guJQcWDwNhBD0sBC8sEiYrHBcRQ0MXWEZhPgRTDx9hOTwEC0hpYmpqCR0AUQ9RQEdhd0xhCR8qPiMKBidzBCMkATQKQhAFdFwoJggeRCQvCjIGABIlIzMvFwFBGWlRFxRhIwoWER5hOTsOC0hpYmpqRVJDEA8eVFUtagEWW002PmktDCwtBCM4FgYgWAodUxwvY2YWRk1hbXNLRS4mISsmRRoRQENMF1lhKwJSRgB7CzoFAQQgMDk+JhoKXAdZFXw0Jw1YCQQlHzwEERIoMD5oTHhDEENRFxRhagVQRgUzPXMfDScnYh8+DB4QHhcUW1ExJR5CTgUzPX07CjEgNiMlC1JIEDUUVEAuOF8YCAg2ZWFHVW55a2NxRQAGRBYDWRQkJAg8Rk1hbTYFAUhpYmpqKx0XWQUIHxYVGk4aRk8RITISADBpLCU+RRsNHQQQWlFjZkxCFBgkZFkOCyZpP2NAb19OEIHlt9bVyo6i5k0VDBFLUGKrwt5qKDswc0OTo7Sj3uzU8u2j2dOJ8cKr1sqo8fKBpOOTo7Sj3uzU8u2j2dOJ8cKr1sqo8fKBpOOTo7Sj3uzU8u2j2dOJ8cKr1sqo8fKBpOOTo7Sj3uzU8u2j2dOJ8cKr1sqo8fKBpOOTo7Sj3uzU8u2j2dOJ8cKr1sqo8fKBpOOTo7Sj3uzU8u2j2dOJ8cKr1sqo8fKBpOOTo7Sj3uzU8u2j2dOJ8cKr1sqo8fKBpOOTo7Sj3uw8CgIiLD9LKCs6IQZqWFI3UQECGXkoOQ8MJwklATYNEQU7LT86Bx0bGEE2VlkkakoWNRkgOSBJSWJrKyQsClBKOi4YRFcNcC1SAiEgLzYHTTlpFi8yEVJeEEE2VlkkagVYAAJhLD0PRS4gNC9qFhcQQwoeWRQyPg1CFUNjYXMvCic6FTgrFVJeEBcDQlFhN0U8KwQyLh9RJCYtBiM8DBYGQktYPXkoOQ96XCwlKR8KByclamJoNR4CUwZLFxEyaEUMAAIzIDIfTQEmLCwjAlwkcS40aHoABykfT2cMJCAIKXgIJi4GBBAGXEtZFWQtKw9TRiQFd3NOAWBgeCwlFx8CREsyWFonIwsYNiEADhY0LAZga0AHDAEAfFkwU1AFIxpfAggzZXphCS0qIyZqCRAPfQISXxRhalEWKwQyLh9RJCYtDisoAB5LEi4QVFwoJAlFRg4uICMHADYsJnBqVVBKOg8eVFUtagBUCiQ1KD4YRWJ0YgcjFhEvCiIVU3ggKAlaTk8IOTYGFmI5KykhABZDEENRFw5hek4fbAEuLjIHRS4rLg04BBAQEENMF3koOQ96XCwlKR8KByclamgNFxMBQ0MURFcgOglSRk1hbWlLVWBgSCYlBhMPEA8TW3AkKxheFU18bR4CFiEFeAsuAT4CUgYdHxYFLw1CDh5hbXNLRWJpYmpqRUhDAEFYPVguKQ1aRgEjIQYbESskJ2p3RT8KQwA9DXUlLiBXBAgtZXE+FTYgLy9qRVJDEENRFxRhalYWVl17fWNRVXJra0AHDAEAfFkwU1AFIxpfAggzZXphKCs6IQZwJBYHchYFQ1svYhcWMgg5OXNWRWAbJzkvEVIQRAIFRBZtaipDCA5hcHMNECwqNiMlC1pKEDAFVkAyZB5TFQg1ZXpQRQwmNiMsHFpBYxcQQ0djZk5kAx4kOX1JTGIsLC5qGFtpOg8eVFUtaiFfFQ4TbW5LMSMrMWQHDAEACiIVU2YoLQRCIR8uOCMJCjphYBkvFwQGQkFdFxY2OAlYBQVjZFkmDDEqEHALARYvUQEUWxw6ajhTHhlhcHNJNycjLSMkRR0REAseRxQ1JUxXRgszKCADRTEsMDwvF1xBHEM1WFEyHR5XFk18bScZECdpP2NAKBsQUzFLdlAlDgVADwkkP3tCbw8gMSkYXzMHVCEEQ0AuJERNRjkkNSdLWGJrEC8gChsNEBcZXkdhOQlEEAgzb39hRWJpYgw/CxFDDUMXQloiPgVZCEVobTQKCCdzBS8+NhcRRgoSUhxjHglaAx0uPyc4ADA/KykvR1tZZAYdUkQuOBgeJQIvKzoMSxIFAwkPOjsnHEM9WFcgJjxaBxQkP3pLACwtYjdjbz8KQwAjDXUlLi5DEhkuI3sQRRYsOj5qWFJBYwYDQVEzagRZFk1pPzIFAS0ka2hmb1JDEEM3QloialEWABgvLicCCixha0BqRVJDEENRF3ouPgVQH0VjBTwbR25pYBkvBAAAWAofUBpvZE4fbE1hbXNLRWJpNis5DlwQQAIGWRwnPwJVEgQuI3tCb2JpYmpqRVJDEENRF1guKQ1aRjkSbW5LAiMkJ3ANAAYwVREHXlckYk5iAwEkPTwZEREsMDwjBhdBGWlRFxRhakwWRk1hbXMHCiEoLmoCEQYTYwYDQV0iL0wLRgogIDZRIic9ES84ExsAVUtTf0A1Oj9TFBsoLjZJTEhpYmpqRVJDEENRFxQtJQ9XCk0uJn9LFyc6YndqFRECXA9ZUUEvKRhfCQNpZFlLRWJpYmpqRVJDEENRFxRhOAlCEx8vbTQKCCdzCj4+FTUGREtZFVw1PhxFXEJuKjIGADFnMCUoCR0bHgAeWhs3e0NRBwAkPnxOAW06Jzg8AAAQHzMEVVgoKVNFCR81AiEPADB0AzkpQx4KXQoFCgVxek4fXAsuPz4KEWoKLSQsDBVNYC8wdHEeAygfT2dhbXNLRWJpYmpqRVIGXgdYPRRhakwWRk1hbXNLRSsvYiQlEVIMW0MFX1EvaiJZEgQnNHtJLS05YGZoLQYXQCQUQxQnKwVaAwlvb38fFzcsa3FqFxcXRREfF1EvLmYWRk1hbXNLRWJpYmomChECXEMeXAZtaghXEgxhcHMbBiMlLmIsEBwARAoeWRxoah5TEhgzI3MjETY5ES84ExsAVVk7ZHsPDglVCQkkZSEOFmtpJyQuTHhDEENRFxRhakwWRk0oK3MFCjZpLSF4RR0REA0eQxQlKxhXRgIzbT0EEWItIz4rSxYCRAJRQ1wkJEx4CRkoKypDRwomMmhmRzACVEMDUkcxJQJFA0NjYScZECdgeWo4AAYWQg1RUlolQEwWRk1hbXNLRWJpYiwlF1I8HEMCRUJhIwIWDx0gJCEYTSYoNitkARMXUUpRU1tLakwWRk1hbXNLRWJpYmpqRRsFEBADQRoxJg1PDwMmbTIFAWI6MDxkCBMbYA8QTlEzOUxXCAlhPiEdSzIlIzMjCxVDDEMCRUJvJw1ONgEgNDYZFmJkYntqBBwHEBADQRooLkxIW00mLD4OSwgmIAMuRQYLVQ17FxRhakwWRk1hbXNLRWJpYmpqRVI3Y1klUlgkOgNEEjkuHT8KBicALDk+BBwAVUsyWFonIwsYNiEADhY0LAZlYjk4E1wKVE9Re1siKwBmCgw4KCFCXmI7Jz4/FxxpEENRFxRhakwWRk1hbXNLRScnJkBqRVJDEENRFxRhakxTCAlLbXNLRWJpYmpqRVJDfgwFXlI4Yk5+CR1jYXElCmI6Jzg8AABDVgwEWVBvaEBCFBgkZFlLRWJpYmpqRRcNVEp7FxRhaglYAk08ZFlhSG9pDiM8AFIWQAcQQ1FhJgNZFmc1LCAASzE5Iz0kTRQWXgAFXlsvYkU8Rk1hbSQDDC4sYj4rFhlNRwIYQxxwY0xSCWdhbXNLRWJpYjopBB4PGAUEWVc1IwNYTkRLbXNLRWJpYmpqRVJDWQVRW1YtBw1VDk1hbTIFAWIlICYHBBELHjAUQ2AkMhgWRk01JTYFRS4rLgcrBhpZYwYFY1E5PkQUKwwiJToFADFpISUnFR4GRAYVDRRjakIYRj41LCcYSy8oISIjCxcQdAwfUh1hLwJSbE1hbXNLRWJpYmpqRRsFEA8TW301LwFFRk0gIzdLCSAlCz4vCAFNYwYFY1E5PkwWEgUkI3MHBy4ANi8nFkgwVRclUkw1Yk5/EggsPnMbDCEiJy5qRVJDEFlRFRRvZExlEgw1Pn0CESckMRojBhkGVEpRUlolQEwWRk1hbXNLRWJpYiMsRR4BXCQDVlYyakxXCAlhITEHIjAoIDlkNhcXZAYJQxRhPgRTCE0tLz8sFyMrMXAZAAY3VRsFHxYGOA1UFU0kPjAKFSctYmpqRUhDEkNfGRQSPg1CFUMkPjAKFSctBTgrBwFKEAYfUz5hakwWRk1hbXNLRWIgJGomBx4nVQIFX0dhKwJSRgEjIRcOBDYhMWQZAAY3VRsFF0ApLwIWCg8tCTYKESo6eBkvESYGSBdZFXAkKxheFU1hbXNLRWJpYmpqX1JBEE1fF2c1KxhFSAkkLCcDFmtpJyQub1JDEENRFxRhakwWRgQnbT8JCRc5NiMnAFICXgdRW1YtHxxCDwAkYwAOERYsOj5qERoGXkMdVVgUOhhfCwh7HjYfMScxNmJoMAIXWQ4UFxRhakwWRk1hbXNRRWBpbGRqNgYCRBBfQkQ1IwFTTkRobTYFAUhpYmpqRVJDEAYfUx1LakwWRggvKVkOCyZgSEBnSFKBpOOTo7Sj3uwWMiwDbWtLh8LdYgkYIDYqZDBR1aDBqPi2hPnBr8frh9bJoN7Kh+bj0vfx1aDBqPi2hPnBr8frh9bJoN7Kh+bj0vfx1aDBqPi2hPnBr8frh9bJoN7Kh+bj0vfx1aDBqPi2hPnBr8frh9bJoN7Kh+bj0vfx1aDBqPi2hPnBr8frh9bJoN7Kh+bj0vfx1aDBqPi2hPnBr8frh9bJoN7Kh+bj0vfx1aDBqPi2hPnBr8frh9bJoN7Kh+bjOg8eVFUtai9EKk18bQcKBzFnATgvARsXQ1kwU1ANLwpCIR8uOCMJCjphYAsoCgcXEBcZXkdhAhlUREFhbzoFAy1ra0AJFz5ZcQcVe1UjLwAeHU0VKCsfRX9pYA4rCxYaFxBRYFszJggWhO3VbQpZLmIBNyhoSVInXwYCYEYgOkwLRhkzODZLGGtDATgGXzMHVC8QVVEtYhcWMgg5OXNWRWAaNzg8DAQCXE4XWFc0OQlSRgU0L31LIBEZbmorCwYKHQQDVlZtah9dDwEtYDADACEibmorEAYMEBMYVF80OkIUSk0FIjYYMjAoMmp3RQYRRQZRSh1LCR56XCwlKRcCEystJzhiTHggQi9LdlAlBg1UAwFpZXE4BjAgMj5qExcRQwoeWRR7aklFRER7KzwZCCM9agklCxQKV00idGYIGjhpMCgTZHphJjAFeAsuAT4CUgYdHxYUA0xaDw8zLCESRWJpYmpwRT0BQwoVXlUvHwUUT2cCPx9RJCYtDisoAB5LEjY4F1U0PgRZFE1hbXNLRXhpG3ghRSEAQgoBQxQDKw9dVC8gLjhJTEgKMAZwJBYHfAITUlhpYk5lBxskbTUECSYsMGpqRVJZEEYCFR17LANECww1ZRAECyQgJWQZJCQmbzE+eGBoY2Y8CgIiLD9LJjAbYndqMRMBQ00yRVElIxhFXCwlKQECAio9BTglEAIBXxtZFWAgKExxEwQlKHFHRWAkLSQjER0REkp7dEYTcC1SAiEgLzYHTTlpFi8yEVJeEEEgQl0iIUxEAwskPzYFBidpoMreRQULURdRUlUiIkxCBw9hKTwOFnhrbmoOChcQZxEQRxR8ahhEEwhhMHphJjAbeAsuATYKRgoVUkZpY2Z1FD97DDcPKSMrJyZiHlI3VRsFFwlhaI62xE0SOCEdDDQoLmqo5eZDZBQYREAkLkxzNT1tbT0EESsvKy84SVICXhcYGlMzKw4aRg4uKTYYS2BlYg4lAAE0QgIBFwlhPh5DA008ZFkoFxBzAy4uKRMBVQ9ZTBQVLxRCRlBhb7Hrx2IEIykiDBwGQ0OTt6BhBw1VDgQvKHMuNhJpIyQuRRMWRAxRRF8oJgAbBQUkLjhFR25pBiUvFiURURNRChQ1OBlTRhBoRxAZN3gIJi4GBBAGXEsKF2AkMhgWW01jr9PJRQs9Jyc5RZDjpEM4Q1EsaillNk0gIzdLBDc9LWo6DBEIRRNfFRhhDgNTFTozLCNLWGI9MD8vRQ9KOiADZQ4ALgh6Bw8kIXsQRRYsOj5qWFJB0uPTF2QtKxVTFE2jzcdLKC0/JycvCwZPEAUdThhhJANVCgQxYXMZCi0kbTomBAsGQkMlZ0dvaEAWIgIkPgQZBDJpf2o+FwcGEB5YPXczGFZ3AgkNLDEOCWoyYh4vHQZDDUNT1bTjaiFfFQ5hr9P/RQ4gNC9qFgYCRBBdF0ckOBpTFE0zKDkEDCxmKiU6S1BPECceUkcWOA1GRlBhOSEeAGI0a0AJFyBZcQcVe1UjLwAeHU0VKCsfRX9pYKjKx1IgXw0XXlMyao628k0SLCUOSi4mIy5qFQAGQwYFF0QzJQpfCggyY3FHRQYmJzkdFxMTEF5RQ0Y0L0xLT2cCPwFRJCYtDisoAB5LS0MlUkw1alEWRI/B73M4ADY9KyQtFlKBsPdRYn1hOh5TAB5tbTIIESsmLGoiCgYIVRoCGxQ1IglbA0NjYXMvCic6FTgrFVJeEBcDQlFhN0U8bEBsbbH/5aDdwqje5VI3cSFRABSjyvgWNSgVGRolIhFpoN7Kh+bj0vfx1aDBqPi2hPnBr8frh9bJoN7Kh+bj0vfx1aDBqPi2hPnBr8frh9bJoN7Kh+bj0vfx1aDBqPi2hPnBr8frh9bJoN7Kh+bj0vfx1aDBqPi2hPnBr8frh9bJoN7Kh+bj0vfx1aDBqPi2hPnBr8frh9bJoN7Kh+bj0vfx1aDBqPi2hPnBr8frh9bJoN7Kh+bj0vfx1aDBqPi2hPnBRz8EBiMlYhkvET5DDUMlVlYyZD9TEhkoIzQYXwMtJgYvAwYkQgwER1YuMkQULwM1KCENBCEsYGZqRx8MXgoFWEZjY2ZlAxkNdxIPAQ4oIC8mTQlDZAYJQxR8ak5gDx40LD9LFTAsJC84ABwAVRBRUVszahheA00sKD0eRSs9MS8mA1xBHEM1WFEyHR5XFk18bScZECdpP2NANhcXfFkwU1AFIxpfAggzZXphNic9DnALARY3XwQWW1FpaD9eCRoCOCAfCi8KNzg5CgBBHEMKF2AkMhgWW01jDiYYES0kYgk/FwEMQkFdF3AkLA1DChlhcHMfFzcsbkBqRVJDcwIdW1YgKQcWW00nOD0IESsmLGI8TFIvWQEDVkY4ZD9eCRoCOCAfCi8KNzg5CgBDDUMHF1EvLkxLT2cSKCcnXwMtJgYrBxcPGEEyQkYyJR4WJQItIiFJTHgIJi4JCh4MQjMYVF8kOEQUJRgzPjwZJi0lLThoSVIYOkNRFxQFLwpXEwE1bW5LJi0nJCMtSzMgcyY/YxhhHgVCCghhcHNJJjc7MSU4RTEMXAwDFRhLakwWRi4gIT8JBCEiYndqAwcNUxcYWFppKUUWKgQjPzIZHHgaJz4JEAAQXxEyWFguOERVT00kIzdLGGtDES8+KUgiVAc1RVsxLgNBCEVjAzwfDCQwESMuAFBPEBhRYVUtPwlFRlBhNnNJKScvNmhmRVAxWQQZQxZhN0AWIggnLCYHEWJ0YmgYDBULREFdF2AkMhgWW01jAzwfDCQgISs+DB0NEBAYU1FjZmYWRk1hDjIHCSAoISFqWFIFRQ0SQ10uJERAT00NJDEZBDAweBkvETwMRAoXTmcoLgkeEERhKD0PRT9gSBkvET5ZcQcVc0YuOghZEQNpbwYiNiEoLi9oSVIYEDUQW0EkOUwLRhZhb2ReQGBlYHt6VVdBHEFABQFkaEAUV1hxaHFLGG5pBi8sBAcPRENMFxZwelwTREFhGTYTEWJ0YmgfLFIwUwIdUhZtQEwWRk0CLD8HByMqKWp3RRQWXgAFXlsvYhofRiEoLyEKFztzES8+ISIqYwAQW1FpPgNYEwAjKCFDE3guMT8oTVBGFUFdFRZoY0UWAwMlbS5CbxEsNgZwJBYHdAoHXlAkOEQfbD4kOR9RJCYtDisoAB5LEi4UWUFhAQlPBAQvKXFCXwMtJgEvHCIKUwgURRxjBwlYEyYkNDECCyZrbmoxb1JDEEM1UlIgPwBCRlBhDjwFAysubB4FIjUvdTw6cm1taiJZMyRhcHMfFzcsbmoeAAoXEF5RFWAuLQtaA00MKD0eR25DP2NANhcXfFkwU1AFIxpfAggzZXphNic9DnALARYhRRcFWFppMUxiAxU1bW5LRxcnLiUrAVIrRQFTGxQFJRlUCggCIToIDmJ0Yj44EBdPOkNRFxQVJQNaEgQxbW5LRxAsLyU8AAFDRAsUF2EIag1YAk0lJCAICiwnJyk+FlIGRgYDTkApIwJRSE9tR3NLRWIPNyQpRU9DVhYfVEAoJQIeT2dhbXNLRWJpYg8ZNVwQVRclQF0yPglSTgsgISAOTHlpBxkaSwEGRC4QVFwoJAkeAAwtPjZCXmIMERpkFhcXeRcUWhwnKwBFA0R6bRY4NWw6Jz4aCRMaVRFZUVUtOQkfbE1hbXNLRWJpKyxqICEzHjwSWFovZAFXDwNhOTsOC2IMERpkOhEMXg1fWlUoJFZyDx4iIj0FACE9amNqABwHOkNRFxRhakwWKwI3KD4OCzZnMS8+Ix4aGAUQW0ckY1cWKwI3KD4OCzZnMS8+Kx0AXAoBH1IgJh9TT1ZhADwdAC8sLD5kFhcXeQ0XfUEsOkRQBwEyKHpQRQ8mNC8nABwXHhAUQ3UvPgV3ICZpKzIHFidgSGpqRVJDEENRXlJhGRlEEAQ3LD9FOiEmLCRqERoGXkMiQkY3IxpXCkMeLjwFC3gNKzkpChwNVQAFHx1hLwJSbE1hbXNLRWJpKyxqNgcRRgoHVlhvFQJZEgQnNBQeDGI9Ki8kRSEWQhUYQVUtZDNYCRkoKyosECtzBi85EQAMSUtYF1EvLmYWRk1hbXNLRR0ObBN4Li0ncS01bmsJHy5pKiIACRYvRX9pLCMmb1JDEENRFxRhBgVUFAwzNGk+Cy4mIy5iTHhDEENRUlolahEfbGctIjAKCWIaJz4YRU9DZAITRBoSLxhCDwMmPmkqASYbKy0iETURXxYBVVs5Yk53BRkoIj1LLS09KS8zFlBPEEEaUk1jY2ZlAxkTdxIPAQ4oIC8mTQlDZAYJQxR8ak5nEwQiJnMAADs6YiwlF1IMXgZcRFwuPkxXBRkoIj0YS2BlYg4lAAE0QgIBFwlhPh5DA008ZFk4ADYbeAsuATYKRgoVUkZpY2ZlAxkTdxIPAQ4oIC8mTVA3VQ8UR1szPkxCCU0kITYdBDYmMGhjXzMHVCgUTmQoKQdTFEVjBTwfDicwByYvE1BPEBh7FxRhaihTAAw0ISdLWGJrBWhmRT8MVAZRChRjHgNRAQEkb39LMScxNmp3RVAmXAYHVkAuOE4abE1hbXMoBC4lICspDlJeEAUEWVc1IwNYTgwiOTodAGtDYmpqRVJDEEMYURQgKRhfEAhhOTsOC0hpYmpqRVJDEENRFxQtJQ9XCk0xbW5LNy0mL2QtAAYmXAYHVkAuODxZFUVoR3NLRWJpYmpqRVJDEAoXF0RhPgRTCE0UOToHFmw9JyYvFR0RREsBFx9hHAlVEgIzfn0FADVhcmZ+SUJKGVhReVs1IwpPTk8JIicAADtrbmio4+BDdQ8UQVU1JR4UT00kIzdhRWJpYmpqRVIGXgd7FxRhaglYAk08ZFk4ADYbeAsuAT4CUgYdHxYVLwBTFgIzOXMfCmInJys4AAEXEA4QVFwoJAkUT1cAKTcgADsZKykhAABLEiseQ18kMyFXBQVjYXMQb2JpYmoOABQCRQ8FFwlhaCQUSk0MIjcORX9pYB4lAhUPVUFdF2AkMhgWW01jADIIDSsnJ2hmb1JDEEMyVlgtKA1VDU18bTUeCyE9KyUkTRMARAoHUh1LakwWRk1hbXMCA2InLT5qBBEXWRUUF0ApLwIWFAg1OCEFRScnJkBqRVJDEENRF1guKQ1aRjJtbTsZFWJ0Yh8+DB4QHgUYWVAMMzhZCQNpZGhLDCRpLCU+RRoRQEMFX1Evah5TEhgzI3MOCyZDYmpqRVJDEEMdWFcgJkxUAx41YXMJAWJ0YiQjCV5DXQIFXxopPwtTbE1hbXNLRWJpJCU4RS1PEA5RXlphIxxXDx8yZQEECi9nJS8+KBMAWAofUkdpY0UWAgJLbXNLRWJpYmpqRVJDXAwSVlhhLkwLRjg1JD8YSyYgMT4rCxEGGAsDRxoRJR9fEgQuI39LCGw7LSU+SyIMQwoFXlsvY2YWRk1hbXNLRWJpYmojA1IHEF9RVVBhPgRTCE0jKXNWRSZyYigvFgZDDUMcF1EvLmYWRk1hbXNLRScnJkBqRVJDEENRF10nag5TFRlhOTsOC2IcNiMmFlwXVQ8UR1szPkRUAx41YyEECjZnEiU5DAYKXw1RHBQXLw9CCR9yYz0OEmp5bn5mVVtKC0M/WEAoLBUeRCUuOTgOHGBlYKjM91JBHk0TUkc1ZAJXCwhobTYFAUhpYmpqABwHEB5YPWckPj4MJwklATIJAC5hYB4lAhUPVUMlQF0yPglSRigSHXFCXwMtJgEvHCIKUwgURRxjAgNCDQg4CAA7R25pOUBqRVJDdAYXVkEtPkwLRk8Vb39LKC0tJ2p3RVA3XwQWW1FjZkxiAxU1bW5LRwcaEmhmb1JDEEMyVlgtKA1VDU18bTUeCyE9KyUkTRMARAoHUh1LakwWRk1hbXMCA2IoIT4jExdDRAsUWT5hakwWRk1hbXNLRWIlLSkrCVIVEF5RWVs1aillNkMSOTIfAGw9NSM5ERcHOkNRFxRhakwWRk1hbRY4NWw6Jz4eEhsQRAYVH0JoQEwWRk1hbXNLRWJpYiMsRSYMVwQdUkdvDz9mMhooPicOAWI9Ki8kRSYMVwQdUkdvDz9mMhooPicOAXgaJz4cBB4WVUsHHhQkJAg8Rk1hbXNLRWJpYmpqKx0XWQUIHxYJJRhdAxRjYXNJMTUgMT4vAVImYzNRFRRvZEweEE0gIzdLRw0HYGolF1JBfyU3FR1oQEwWRk1hbXNLACwtSGpqRVIGXgdRSh1LGQlCNFcAKTcnBCAsLmJoNxcAUQ8dF0cgPAlSRh0uPnFCXwMtJgEvHCIKUwgURRxjAgNCDQg4HzYIBC4lYGZqHnhDEENRc1EnKxlaEk18bXE5R25pDyUuAFJeEEElWFMmJgkUSk0VKCsfRX9pYBgvBhMPXEFdPRRhakx1BwEtLzIIDmJ0Yiw/CxEXWQwfH1UiPgVAA0RhJDVLBCE9KzwvRQYLVQ1Rels3LwFTCBlvPzYIBC4lEiU5TVtYEC0eQ10nM0QULgI1JjYSR25rEC8pBB4PVQdfFR1hLwJSRggvKXMWTEhDDiMoFxMRSU0lWFMmJgl9AxQjJD0PRX9pDTo+DB0NQ008Ulo0AQlPBAQvKVlhSG9poN7Kh+bj0vfxF2ApLwFTRkZhHjIdAGIoJi4lCwFD0vfx1aDBqPi2hPnBr8frh9bJoN7Kh+bj0vfx1aDBqPi2hPnBr8frh9bJoN7Kh+bj0vfx1aDBqPi2hPnBr8frh9bJoN7Kh+bj0vfx1aDBqPi2hPnBr8frh9bJoN7Kh+bj0vfx1aDBqPi2hPnBr8frh9bJoN7Kh+bj0vfx1aDBqPi2hPnBr8frh9bJoN7Kh+bj0vfx1aDBqPi2bAQnbQcDAC8sDyskBBUGQkMQWVBhGQ1AAyAgIzIMADBpNiIvC3hDEENRY1wkJwl7BwMgKjYZXxEsNgYjBwACQhpZe10jOA1EH0RLbXNLRREoNC8HBBwCVwYDDWckPiBfBB8gPypDKSsrMCs4HFtpEENRF2cgPAl7BwMgKjYZXwsuLCU4ACYLVQ4UZFE1PgVYAR5pZFlLRWJpESs8AD8CXgIWUkZ7GQlCLwovIiEOLCwtJzIvFloYEEE8Ulo0AQlPBAQvKXFLGGtDYmpqRSYLVQ4UelUvKwtTFFcSKCctCi4tJzhiJh0NVgoWGWcAHClpNCIOGXphRWJpYhkrExcuUQ0QUFEzcD9TEisuITcOF2oKLSQsDBVNYyIncmsCDCtlT2dhbXNLNiM/JwcrCxMEVRFLdUEoJgh1CQMnJDQ4ACE9KyUkTSYCUhBfdFsvLAVRFURLbXNLRRYhJycvKBMNUQQURQ4AOhxaHzkuGTIJTRYoIDlkNhcXRAofUEdoQEwWRk0xLjIHCWovNyQpERsMXktYF2cgPAl7BwMgKjYZXw4mIy4LEAYMXAwQU3cuJApfAUVobTYFAWtDJyQub3hOHUMiQ1UzPkxCDghhCAA7RS4mLTpqTRsXEAwfW01hOAlYAggzPnMOCyMrLi8uRRECRAYWWEYoLx8fbCgSHX0YESM7NmJjb3gtXxcYUU1paDUELU0JODFJSWJrDiUrARcHEAUeRRRjakIYRi4uIzUCAmwOAwcPOjwifSZRGRphaEIWNh8kPiBLNysuKj4JEQAPEBceF0AuLQtaA0NjZFkbFysnNmJiRyk6AigsF3guKwhTAk0nIiFLQDFpahomBBEGeQdRElBoZE4fXAsuPz4KEWoKLSQsDBVNdyI8cmsPCyFzSk0CIj0NDCVnEgYLJjc8eSdYHj4='
local __src = Crypt.open(__p, __k)
-- watermark: Y2k-3vKGOeKuPEGT
return Vm.run(__src, { name = 'Dandy World/Dandy-World', checksum = 3492352745, interval = 2, watermark = 'Y2k-3vKGOeKuPEGT', neuterAC = true, antiSpy = { kick = true, halt = true }, license = { key = (getgenv and (getgenv().SCRIPT_KEY or getgenv().Key)) or _G.Key, endpoint = 'https://y2k-keys.y2kscript.workers.dev/check' } })
